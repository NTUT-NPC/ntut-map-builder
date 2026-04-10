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
import json
import html
import urllib.parse
from collections import defaultdict
from io import BytesIO
from pathlib import Path

try:
    import requests
    from PIL import Image, ImageDraw, ImageFont
    import urllib3
except ImportError:
    sys.exit("Please install dependencies:  pip install requests Pillow")

# The GeoServer uses a self-signed / internal CA cert — suppress noisy warnings.
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ──────────────────────────── WFS configuration ──────────────────────────────

WFS_BASE    = "https://geoserver.oga.ntut.edu.tw/ows"
WFS_VERSION = "2.0.0"
CRS         = "EPSG:3826"
# Requesting WFS features directly in Web Mercator for easy basemap alignment
WFS_SRS     = "EPSG:3857"

# Campus bounding box in EPSG:3826 (from gis:gis_base + gis:gis_base_en)
CAMPUS_BBOX = {
    "minx": 303793.78125,
    "miny": 2770482.25,
    "maxx": 304353.9375,
    "maxy": 2770802.0,
}

PADDING_RATIO    = 0.05   # 5 % margin so edge labels are not clipped
TARGET_LONG_EDGE = 16000  # target 8K pixels on the longer axis
MAX_FEATURES     = 10000  # GeoServer count limit per request
# Font settings for local labels
LABEL_FONT_SIZE  = 24
FONT_PATH        = "/usr/share/fonts/google-noto-sans-tc-fonts/NotoSansTC-Regular.otf"

# Feature filtering: exclude rooms containing these keywords in room_name, use, or keyword fields.
EXCLUDE_KEYWORDS = [
    "柱子", "走廊", "走道", "梯廳", "管道間", "未命名", "委外空間",
    "排煙", "機房", "採光", "消防", "茶水間", "電氣室", "大廳", "挑空", "管道"
]

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


# ──────────────────────────── WFS helpers ────────────────────────────────────

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


def fetch_json(url: str, retries: int = 3) -> dict:
    for attempt in range(retries):
        try:
            resp = requests.get(url, timeout=120, verify=False)
            resp.raise_for_status()
            return resp.json()
        except Exception as exc:
            print(f"  Attempt {attempt+1} failed: {exc}", file=sys.stderr)
            if attempt == retries - 1:
                raise
    raise RuntimeError("All retries exhausted")


def render_svg(layers: list[str], bbox: dict, width: int, height: int,
               basemap_url: str = None) -> str:
    """Fetch WFS features and generate a standalone SVG string."""
    svg_header = (
        f'<svg width="{width}" height="{height}" viewBox="0 0 {width} {height}" '
        'xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink">\n'
    )
    svg_footer = '</svg>'
    
    # CSS for styling (Modern, Non-Grayscale Palette)
    style = """
    <style>
        .building { fill: #f0f4f8; stroke: #d1dce5; stroke-width: 2; }
        .room     { fill: #ffffff; fill-opacity: 0.8; stroke: #bcccdc; stroke-width: 1; }
        .label    { font-family: "Noto Sans TC", sans-serif; font-size: 24px; fill: #334e68; font-weight: 500; text-anchor: middle; dominant-baseline: middle; }
    </style>
    """
    
    body = [svg_header, style]
    
    # Basemap embedding disabled
    # if basemap_url:
    #     body.append(f'  <image xlink:href="{basemap_url}" width="{width}" height="{height}" />\n')

    # Scaling helpers
    bx_min, bx_max = bbox["minx"], bbox["maxx"]
    by_min, by_max = bbox["miny"], bbox["maxy"]
    bx_span = bx_max - bx_min
    by_span = by_max - by_min

    def to_px(x, y):
        px = (x - bx_min) / bx_span * width
        py = (1.0 - (y - by_min) / by_span) * height
        return f"{px:.2f},{py:.2f}"

    placed_labels = [] # List of (x0, y0, x1, y1)

    for layer in layers:
        layer_id = layer.replace(":", "_")
        body.append(f'  <g id="{layer_id}">\n')
        
        params = {
            "service": "WFS",
            "version": WFS_VERSION,
            "request": "GetFeature",
            "typeNames": layer,
            "outputFormat": "application/json",
            "SRSNAME": WFS_SRS,
            "count": MAX_FEATURES,
        }
        url = WFS_BASE + "?" + urllib.parse.urlencode(params)
        print(f"    Fetching {layer} …", end=" ", flush=True)
        data = fetch_json(url)
        features = data.get("features", [])
        print(f"({len(features)} features) ✓")

        is_building = "building" in layer
        css_class = "building" if is_building else "room"

        for feat in features:
            props = feat.get("properties", {})
            
            # Filtering for room layers
            if not is_building:
                name    = props.get("room_name") or ""
                usage   = props.get("use") or ""
                keyword = props.get("keyword") or ""
                
                if any(k in (name + usage + keyword) for k in EXCLUDE_KEYWORDS):
                    continue

            geom = feat.get("geometry")
            if not geom: continue
            
            polys = []
            if geom["type"] == "Polygon":
                polys = [geom["coordinates"]]
            elif geom["type"] == "MultiPolygon":
                polys = geom["coordinates"]
            
            for poly in polys:
                # Build SVG path data
                d = []
                for ring in poly:
                    pts = [to_px(c[0], c[1]) for c in ring]
                    if not pts: continue
                    d.append(f"M {pts[0]} " + " ".join(f"L {p}" for p in pts[1:]) + " Z")
                
                path_data = " ".join(d)
                body.append(f'    <path class="{css_class}" d="{path_data}" />\n')

            # Raw Labels: no calculations, no wrapping, no truncation, no collision check.
            if not is_building:
                rid   = props.get("room_id") or props.get("id") or ""
                rname = props.get("room_name") or ""
                
                display_name = (rname or rid).strip()
                
                if display_name:
                    f_bbox = feat.get("bbox")
                    if f_bbox:
                        cx, cy = (f_bbox[0]+f_bbox[2])/2, (f_bbox[1]+f_bbox[3])/2
                    else:
                        first_ring = polys[0][0]
                        cx = sum(c[0] for c in first_ring) / len(first_ring)
                        cy = sum(c[1] for c in first_ring) / len(first_ring)
                    
                    xy = to_px(cx, cy).split(",")
                    px, py = float(xy[0]), float(xy[1])
                    
                    body.append(f'    <text x="{px:.2f}" y="{py:.2f}" class="label">{html.escape(display_name)}</text>\n')
        
        body.append('  </g>\n')

    body.append(svg_footer)
    return "".join(body)


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
    ap = argparse.ArgumentParser(description="Render NTUT campus WFS floor maps")
    ap.add_argument("--clean",   action="store_true",
                    help="Delete existing output PNGs and re-render all")
    ap.add_argument("--basemap", action="store_true",
                    help="Ignored (basemap is always used)")
    ap.add_argument("--floor",   metavar="FLOOR",
                    help="Render only this floor (e.g. 1F, B1, RF)")
    args = ap.parse_args()

    print("=== NTUT Campus WFS Floor Map Renderer ===")
    print("    Source : GeoServer WFS (JSON API)")
    print("    Basemap: Carto Voyager (OpenStreetMap)")
    print()

    OUTPUT_DIR.mkdir(exist_ok=True)

    if args.clean:
        # Clean floor-specific output but preserve global basemap and caches
        patterns = ["campus_floor_*.svg", "campus_floor_*.webp", "campus_floor_*.png"]
        removed = []
        for p in patterns:
            removed.extend(list(OUTPUT_DIR.glob(p)))
        for f in removed:
            f.unlink()
        print(f"Cleaned {len(removed)} existing floor maps.\n")

    # Native EPSG:3826 bounds of campus
    bbox_3826 = padded_bbox(CAMPUS_BBOX, PADDING_RATIO)
    wgs84_bbox, merc_bbox = epsg3826_bbox_to_merc(bbox_3826)

    # We shift the WMS request to EPSG:3857 (Web Mercator) so it naturally aligns map
    wms_bbox  = merc_bbox
    wms_crs   = "EPSG:3857"

    canvas_w, canvas_h = compute_canvas_size(wms_bbox, TARGET_LONG_EDGE)
    print(f"Canvas size : {canvas_w} × {canvas_h} px")
    print(f"WFS bbox    : {bbox_str(wms_bbox)}")
    print()

    # Basemap fetching disabled as requested
    # basemap_img = fetch_basemap(wgs84_bbox, merc_bbox, canvas_w, canvas_h)
    # basemap_path = OUTPUT_DIR / "campus_basemap.webp"
    # if not basemap_path.exists() or args.clean:
    #     basemap_img.save(str(basemap_path), format="WEBP", lossless=False, quality=85, method=6)
    #     print(f"  → Saved {basemap_path.name}  ({basemap_path.stat().st_size // 1024} KB)")

    floor_groups = load_floor_groups(ROOM_LIST_FILE)
    print(f"Floors found: {len(floor_groups)}")
    for fl, layers in floor_groups.items():
        print(f"  {fl:>4s}  →  {len(layers):3d} room layers")
    print()

    for floor, room_layers in floor_groups.items():
        if args.floor and floor != args.floor:
            continue

        out_path = OUTPUT_DIR / f"campus_floor_{floor}.svg"
        if out_path.exists() and not args.clean:
            print(f"[{floor}] Already exists, skipping → {out_path.name}")
            continue

        print(f"[{floor}] Generating SVG floor map …")
        svg_content = render_svg(BASE_LAYERS + room_layers, wms_bbox, canvas_w, canvas_h)

        with open(out_path, "w", encoding="utf-8") as f:
            f.write(svg_content)
        print(f"  → Saved {out_path.name}  ({out_path.stat().st_size // 1024} KB)\n")

    import json
    manifest = {
        "basemap": "campus_basemap.webp",
        "floors": {}
    }
    for floor in floor_groups.keys():
        manifest["floors"][floor] = f"campus_floor_{floor}.svg"
        
    manifest_path = OUTPUT_DIR / "manifest.json"
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)
    print(f"  → Saved {manifest_path.name}")

    print("Done!")


if __name__ == "__main__":
    main()
