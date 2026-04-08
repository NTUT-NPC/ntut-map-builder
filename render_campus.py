#!/usr/bin/env python3
# ruff: noqa: S501  (SSL verify=False is intentional for self-signed campus cert)
"""
render_campus.py
================
Renders NTUT campus floor maps from the GeoServer WMS API.
Each output PNG contains ALL buildings at a given floor level (e.g. 1F, 2F, B1, RF, …).
Resolution target: 8K-ish canvas keeping aspect ratio.

Usage
-----
  python render_campus.py                     # render all floors
  python render_campus.py --clean             # delete existing and re-render
  python render_campus.py --floor 1F          # single floor only

Requirements: pip install requests Pillow
"""

import re
import sys
import math
import urllib.parse
from collections import defaultdict
from io import BytesIO
from pathlib import Path

try:
    import requests
    from PIL import Image
    import urllib3
except ImportError:
    sys.exit("Please install dependencies:  pip install requests Pillow")

# The GeoServer uses a self-signed / internal CA cert — suppress noisy warnings.
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ──────────────────────────── WMS configuration ──────────────────────────────

WMS_BASE    = "https://geoserver.oga.ntut.edu.tw/wms"
WMS_VERSION = "1.1.1"
CRS         = "EPSG:3826"
IMAGE_FORMAT = "image/png8"

# Campus bounding box in EPSG:3826 (from gis:gis_base + gis:gis_base_en)
CAMPUS_BBOX = {
    "minx": 303793.78125,
    "miny": 2770482.25,
    "maxx": 304353.9375,
    "maxy": 2770802.0,
}

PADDING_RATIO    = 0.05   # 5 % margin so edge labels are not clipped
TARGET_LONG_EDGE = 16000  # target 8K pixels on the longer axis
MAX_TILE_SIZE    = 4096  # GeoServer tile limit per request
RENDER_DPI       = 120   # GeoServer DPI hint → balance text size to prevent collision/hiding

# Base WMS layers (always included, bottom → top)
BASE_LAYERS = [
    "gis:gis_building_geom",
]

ROOM_LIST_FILE = Path(__file__).parent / "room.txt"
OUTPUT_DIR     = Path(__file__).parent / "output"

# ──────────────────────── Basemap (OpenStreetMap / Carto) ────────────────────

# Carto Voyager — colored map, high detail
BASEMAP_URL    = "https://a.basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}@2x.png"
BASEMAP_ZOOM   = 19    # zoom 19 ≈ 0.3 m/px at lat 25°N
TILE_PX        = 512   # @2x tile = 512 px
TILE_CACHE_DIR = OUTPUT_DIR / ".tile_cache"
BASEMAP_UA     = "NTUT-CampusFloorRenderer/1.0 (educational)"

MERC_R = 6378137.0   # Web Mercator / GRS80 semi-major axis (metres)


# ─────────── Projection helpers: EPSG:3826 ↔ WGS84 ↔ Web Mercator ───────────

def _epsg3826_to_wgs84(E: float, N: float) -> tuple[float, float]:
    """
    Inverse EPSG:3826 (TWD97 TM2, central meridian 121°E) → (lon°, lat°).
    Uses the USGS series expansion; accurate to <1 mm.
    """
    a   = 6378137.0          # GRS80 semi-major axis
    f   = 1 / 298.257222101  # GRS80 flattening
    e2  = 2*f - f*f
    k0  = 0.9999
    lon0 = math.radians(121.0)
    x = E - 250000.0         # remove false easting
    M = N / k0               # meridional arc (false northing = 0)
    mu = M / (a * (1 - e2/4 - 3*e2**2/64 - 5*e2**3/256))
    e1 = (1 - math.sqrt(1-e2)) / (1 + math.sqrt(1-e2))
    phi1 = (mu
            + (3*e1/2   - 27*e1**3/32)   * math.sin(2*mu)
            + (21*e1**2/16 - 55*e1**4/32) * math.sin(4*mu)
            + (151*e1**3/96)               * math.sin(6*mu)
            + (1097*e1**4/512)             * math.sin(8*mu))
    N1  = a / math.sqrt(1 - e2 * math.sin(phi1)**2)
    T1  = math.tan(phi1)**2
    C1  = e2/(1-e2) * math.cos(phi1)**2
    R1  = a*(1-e2) / (1 - e2 * math.sin(phi1)**2)**1.5
    D   = x / (N1 * k0)
    phi = phi1 - (N1 * math.tan(phi1) / R1) * (
          D**2/2
        - (5 + 3*T1 + 10*C1 - 4*C1**2 - 9*e2/(1-e2)) * D**4/24
        + (61 + 90*T1 + 298*C1 + 45*T1**2 - 252*e2/(1-e2) - 3*C1**2) * D**6/720)
    lam = lon0 + (
          D
        - (1 + 2*T1 + C1) * D**3/6
        + (5 - 2*C1 + 28*T1 - 3*C1**2 + 8*e2/(1-e2) + 24*T1**2) * D**5/120
    ) / math.cos(phi1)
    return math.degrees(lam), math.degrees(phi)   # (lon, lat)


def _lon_to_merc(lon: float) -> float:
    return math.radians(lon) * MERC_R


def _lat_to_merc(lat: float) -> float:
    return math.log(math.tan(math.pi / 4 + math.radians(lat) / 2)) * MERC_R


def epsg3826_bbox_to_merc(bbox_3826: dict) -> tuple[dict, dict]:
    """
    Convert an EPSG:3826 bbox to (wgs84_bbox, merc_bbox).
    Uses proper inverse TM projection for accuracy.
    """
    lon0, lat0 = _epsg3826_to_wgs84(bbox_3826["minx"], bbox_3826["miny"])
    lon1, lat1 = _epsg3826_to_wgs84(bbox_3826["maxx"], bbox_3826["maxy"])
    wgs84 = {"minx": lon0, "miny": lat0, "maxx": lon1, "maxy": lat1}
    merc  = {
        "minx": _lon_to_merc(lon0), "miny": _lat_to_merc(lat0),
        "maxx": _lon_to_merc(lon1), "maxy": _lat_to_merc(lat1),
    }
    return wgs84, merc


def _lon_to_tx(lon: float, zoom: int) -> int:
    return int((lon + 180) / 360 * (2 ** zoom))


def _lat_to_ty(lat: float, zoom: int) -> int:
    lat_r = math.radians(lat)
    return int((1 - math.asinh(math.tan(lat_r)) / math.pi) / 2 * (2 ** zoom))


def _tile_merc_bounds(tx: int, ty: int, zoom: int) -> tuple[float, float, float, float]:
    """(x_min, y_min, x_max, y_max) in Web Mercator metres for one tile."""
    n  = 2 ** zoom
    x0 = (tx     / n * 2 - 1) * math.pi * MERC_R
    x1 = ((tx+1) / n * 2 - 1) * math.pi * MERC_R
    y1 = (1 - 2 *  ty    / n) * math.pi * MERC_R   # north edge
    y0 = (1 - 2 * (ty+1) / n) * math.pi * MERC_R   # south edge
    return x0, y0, x1, y1


def _fetch_basemap_tile(z: int, x: int, y: int) -> Image.Image:
    TILE_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache = TILE_CACHE_DIR / f"voyager_{z}_{x}_{y}.png"
    if cache.exists():
        return Image.open(cache).convert("RGBA")
    url  = BASEMAP_URL.format(z=z, x=x, y=y)
    resp = requests.get(url, timeout=30, headers={"User-Agent": BASEMAP_UA})
    resp.raise_for_status()
    img  = Image.open(BytesIO(resp.content)).convert("RGBA")
    img.save(str(cache), format="PNG")
    return img


def fetch_basemap(wgs84: dict, merc: dict, canvas_w: int, canvas_h: int,
                  zoom: int = BASEMAP_ZOOM) -> Image.Image:
    """
    Fetch Carto Light OSM tiles and strictly crop out the Web Mercator bounds.
    Scale to match the requested canvas pixel size.
    """
    tx0 = _lon_to_tx(wgs84["minx"], zoom)
    tx1 = _lon_to_tx(wgs84["maxx"], zoom)
    ty0 = _lat_to_ty(wgs84["maxy"], zoom) - 1   # extra tile north
    ty1 = _lat_to_ty(wgs84["miny"], zoom) + 1   # extra tile south

    n_tiles = (tx1-tx0+1) * (ty1-ty0+1)
    print(f"  Fetching {n_tiles} basemap tiles (z{zoom}) …", end=" ", flush=True)

    grid_w = (tx1-tx0+1) * TILE_PX
    grid_h = (ty1-ty0+1) * TILE_PX
    grid   = Image.new("RGB", (grid_w, grid_h), (220, 220, 220))
    for ty in range(ty0, ty1+1):
        for tx in range(tx0, tx1+1):
            try:
                tile = _fetch_basemap_tile(zoom, tx, ty).convert("RGB")
            except Exception as exc:
                print(f"\n    ⚠ {tx}/{ty}: {exc}", file=sys.stderr)
                tile = Image.new("RGB", (TILE_PX, TILE_PX), (220, 220, 220))
            grid.paste(tile, ((tx-tx0)*TILE_PX, (ty-ty0)*TILE_PX))

    # Full grid Mercator extent
    gx0, _,   _,   _   = _tile_merc_bounds(tx0, ty0, zoom)
    _,   _,   gx1, _   = _tile_merc_bounds(tx1, ty0, zoom)
    _,   _,   _,   gy1 = _tile_merc_bounds(tx0, ty0, zoom)   # north
    _,   gy0, _,   _   = _tile_merc_bounds(tx0, ty1, zoom)   # south
    gx_span = gx1 - gx0
    gy_span = gy1 - gy0

    # ── Crop to exact Mercator bounds ─────────────────────────────────────────
    mx0, mx1 = merc["minx"], merc["maxx"]
    my0, my1 = merc["miny"], merc["maxy"]

    cx0 = max(0,      int((mx0 - gx0) / gx_span * grid_w))
    cx1 = min(grid_w, int((mx1 - gx0) / gx_span * grid_w))
    cy0 = max(0,      int((gy1 - my1) / gy_span * grid_h))
    cy1 = min(grid_h, int((gy1 - my0) / gy_span * grid_h))

    out = grid.crop((cx0, cy0, cx1, cy1))

    # Scale to canvas size
    if out.size != (canvas_w, canvas_h):
        out = out.resize((canvas_w, canvas_h), Image.LANCZOS)

    print("✓")
    return out


# ──────────────────────────── WMS helpers ────────────────────────────────────

def padded_bbox(bbox: dict, ratio: float) -> dict:
    w = bbox["maxx"] - bbox["minx"]
    h = bbox["maxy"] - bbox["miny"]
    dx, dy = w * ratio, h * ratio
    return {
        "minx": bbox["minx"] - dx, "miny": bbox["miny"] - dy,
        "maxx": bbox["maxx"] + dx, "maxy": bbox["maxy"] + dy,
    }


def compute_canvas_size(bbox: dict, long_edge: int) -> tuple[int, int]:
    w = bbox["maxx"] - bbox["minx"]
    h = bbox["maxy"] - bbox["miny"]
    aspect = w / h
    if aspect >= 1:
        return long_edge, max(1, round(long_edge / aspect))
    return max(1, round(long_edge * aspect)), long_edge


def bbox_str(bbox: dict) -> str:
    return f"{bbox['minx']},{bbox['miny']},{bbox['maxx']},{bbox['maxy']}"


def build_wms_url(layers: list[str], bbox: dict, width: int, height: int,
                  transparent: bool = True, crs: str = CRS) -> str:
    params = {
        "SERVICE":        "WMS",
        "VERSION":        WMS_VERSION,
        "REQUEST":        "GetMap",
        "LAYERS":         ",".join(layers),
        "STYLES":         ",".join([""] * len(layers)),
        "SRS":            crs,
        "BBOX":           bbox_str(bbox),
        "WIDTH":          str(width),
        "HEIGHT":         str(height),
        "FORMAT":         IMAGE_FORMAT,
        "TRANSPARENT":    "true" if transparent else "false",
        "FORMAT_OPTIONS": f"dpi:{RENDER_DPI}",
    }
    return WMS_BASE + "?" + urllib.parse.urlencode(params)


def fetch_image(url: str, retries: int = 3) -> Image.Image:
    for attempt in range(retries):
        try:
            resp = requests.get(url, timeout=120, verify=False)
            resp.raise_for_status()
            ct = resp.headers.get("Content-Type", "")
            if "image" not in ct:
                raise ValueError(f"Non-image response ({ct}): {resp.text[:200]}")
            return Image.open(BytesIO(resp.content)).convert("RGBA")
        except Exception as exc:
            print(f"  Attempt {attempt+1} failed: {exc}", file=sys.stderr)
            if attempt == retries - 1:
                raise
    raise RuntimeError("All retries exhausted")


def render_wms(layers: list[str], bbox: dict, width: int, height: int,
               crs: str = CRS) -> Image.Image:
    """Fetch WMS, tiling into sub-requests if needed (GeoServer ≤ MAX_TILE_SIZE px)."""
    if width <= MAX_TILE_SIZE and height <= MAX_TILE_SIZE:
        url = build_wms_url(layers, bbox, width, height, crs=crs)
        print(f"    GET {width}×{height} …", end=" ", flush=True)
        img = fetch_image(url)
        print("✓")
        return img

    cols = math.ceil(width  / MAX_TILE_SIZE)
    rows = math.ceil(height / MAX_TILE_SIZE)
    canvas = Image.new("RGBA", (width, height), (255, 255, 255, 0))
    bx_span = bbox["maxx"] - bbox["minx"]
    by_span = bbox["maxy"] - bbox["miny"]

    for row in range(rows):
        for col in range(cols):
            px0 = col * MAX_TILE_SIZE
            px1 = min(px0 + MAX_TILE_SIZE, width)
            py0 = row * MAX_TILE_SIZE
            py1 = min(py0 + MAX_TILE_SIZE, height)
            tw, th = px1 - px0, py1 - py0
            f_x0 = px0 / width
            f_x1 = px1 / width
            f_y1 = 1.0 - (py0 / height)
            f_y0 = 1.0 - (py1 / height)
            sub_bbox = {
                "minx": bbox["minx"] + f_x0 * bx_span,
                "maxx": bbox["minx"] + f_x1 * bx_span,
                "miny": bbox["miny"] + f_y0 * by_span,
                "maxy": bbox["miny"] + f_y1 * by_span,
            }
            url = build_wms_url(layers, sub_bbox, tw, th, crs=crs)
            print(f"    tile [{row},{col}] {tw}×{th} …", end=" ", flush=True)
            canvas.paste(fetch_image(url), (px0, py0))
            print("✓")

    return canvas


# ────────────────────────── layer grouping ───────────────────────────────────

FLOOR_ORDER = [
    "B5", "B4", "B3", "B2", "B1", "1F",
    "2F", "3F", "4F", "5F", "6F", "7F", "8F", "9F",
    "10F", "11F", "12F", "13F", "14F", "15F", "16F",
    "R1", "R2", "R3", "RF",
]

def floor_sort_key(floor: str) -> int:
    try:
        return FLOOR_ORDER.index(floor)
    except ValueError:
        return len(FLOOR_ORDER) + ord(floor[0])


def load_floor_groups(room_file: Path) -> dict[str, list[str]]:
    """
    Groups layers from room.txt by floor code.
    Skips *M mezzanine floors (B1M, 1M…).
    R1/R2/R3/RF are roof levels (= top floor + 1 of each building).
    """
    groups: dict[str, list[str]] = defaultdict(list)
    pattern = re.compile(r"gis_room:(\w+)_(\w+)")
    with open(room_file, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            m = pattern.fullmatch(line)
            if not m:
                continue
            floor = m.group(2)
            if floor.endswith("M"):   # skip mezzanine floors
                continue
            if floor in ("R1", "R2", "R3"):
                floor = "RF"
            groups[floor].append(line)
    return dict(sorted(groups.items(), key=lambda kv: floor_sort_key(kv[0])))


# ──────────────────────────────── main ───────────────────────────────────────

def main():
    import argparse
    ap = argparse.ArgumentParser(description="Render NTUT campus WMS floor maps")
    ap.add_argument("--clean",   action="store_true",
                    help="Delete existing output PNGs and re-render all")
    ap.add_argument("--basemap", action="store_true",
                    help="Ignored (basemap is always used)")
    ap.add_argument("--floor",   metavar="FLOOR",
                    help="Render only this floor (e.g. 1F, B1, RF)")
    args = ap.parse_args()

    print("=== NTUT Campus WMS Floor Map Renderer ===")
    print("    Basemap: Carto Voyager (OpenStreetMap)")
    print()

    OUTPUT_DIR.mkdir(exist_ok=True)

    if args.clean:
        removed = list(OUTPUT_DIR.glob("campus_*.png")) + list(OUTPUT_DIR.glob("campus_*.webp"))
        for f in removed:
            f.unlink()
        print(f"Cleaned {len(removed)} existing maps.\n")

    # Native EPSG:3826 bounds of campus
    bbox_3826 = padded_bbox(CAMPUS_BBOX, PADDING_RATIO)
    wgs84_bbox, merc_bbox = epsg3826_bbox_to_merc(bbox_3826)

    # We shift the WMS request to EPSG:3857 (Web Mercator) so it naturally aligns map
    wms_bbox  = merc_bbox
    wms_crs   = "EPSG:3857"

    canvas_w, canvas_h = compute_canvas_size(wms_bbox, TARGET_LONG_EDGE)
    print(f"Canvas size : {canvas_w} × {canvas_h} px  (DPI hint: {RENDER_DPI})")
    print(f"WMS bbox    : {bbox_str(wms_bbox)}")
    print(f"Tiling      : {math.ceil(canvas_w/MAX_TILE_SIZE)}×{math.ceil(canvas_h/MAX_TILE_SIZE)} per request")
    print()

    # Pre-fetch and save basemap once
    basemap_img = fetch_basemap(wgs84_bbox, merc_bbox, canvas_w, canvas_h)
    basemap_path = OUTPUT_DIR / "campus_basemap.webp"
    if not basemap_path.exists() or args.clean:
        basemap_img.save(str(basemap_path), format="WEBP", lossless=False, quality=85, method=6)
        print(f"  → Saved {basemap_path.name}  ({basemap_path.stat().st_size // 1024} KB)")
    print()

    floor_groups = load_floor_groups(ROOM_LIST_FILE)
    print(f"Floors found: {len(floor_groups)}")
    for fl, layers in floor_groups.items():
        print(f"  {fl:>4s}  →  {len(layers):3d} room layers")
    print()

    for floor, room_layers in floor_groups.items():
        if args.floor and floor != args.floor:
            continue

        out_path = OUTPUT_DIR / f"campus_floor_{floor}.webp"
        if out_path.exists():
            print(f"[{floor}] Already exists, skipping → {out_path.name}")
            continue

        print(f"[{floor}] Rendering {len(room_layers)} room layers …")
        wms_img = render_wms(BASE_LAYERS + room_layers, wms_bbox, canvas_w, canvas_h,
                             crs=wms_crs)

        # Convert to Grayscale + Alpha to aggressively reduce color space
        wms_img = wms_img.convert("LA")

        # Save as WEBP for much better compression
        wms_img.save(str(out_path), format="WEBP", lossless=True, method=6)
        print(f"  → Saved {out_path.name}  ({out_path.stat().st_size // 1024} KB)\n")

    import json
    manifest = {
        "basemap": "campus_basemap.webp",
        "floors": {}
    }
    for floor in floor_groups.keys():
        manifest["floors"][floor] = f"campus_floor_{floor}.webp"
        
    manifest_path = OUTPUT_DIR / "manifest.json"
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)
    print(f"  → Saved {manifest_path.name}")

    print("Done!")


if __name__ == "__main__":
    main()
