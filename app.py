"""CampusBin - Smart Waste Collection & Route Optimization
SOCIOTHON 2026 - Problem Statement 2 - IIT Roorkee

* 30 bins are picked from data/campus.kml (or campus.kmz); only placemarks
  INSIDE the IIT Roorkee campus box are used.
* Routes follow the real OpenStreetMap road network
  (cached in data/roads.json, downloaded from Overpass if missing).

Run:
    python -m pip install -r requirements.txt
    python app.py          ->  http://localhost:5000
"""
import json
import math
import os
import random
import threading
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile

import networkx as nx
from flask import Flask, jsonify, request, send_from_directory

app = Flask(__name__, static_folder="static")
random.seed(7)
LOCK = threading.RLock()
BASE = os.path.dirname(os.path.abspath(__file__))     # data/ is found no matter where the app is started from

# =====================================================================
# CONFIG
# =====================================================================
N_BINS = 30                                          # exactly this many bins are used
CAMPUS_BOX = (29.8590, 77.8890, 29.8720, 77.9030)    # (south, west, north, east) = IIT Roorkee
MUST_KEEP_FOLDER = "dustbin"                         # KML folder whose bins are always kept
DEDUPE_M = 30                                        # placemarks closer than this = same bin
DEPOT_LATLON = None                                  # e.g. (29.8650, 77.8960); None -> "Depot" placemark, else centre of bins

SIM_SPEED = 60                                       # 1 real second = 1 simulated minute
TRUCK_CAP_L = 1500                                   # litres per trip
TRUCK_KMH = 18                                       # average campus speed
STOP_MIN = 3                                         # minutes spent at each bin
FUEL_L_PER_KM = 0.40
CO2_KG_PER_L = 2.68
ROAD_FACTOR = 1.3                                    # only used if no road data is available

# Assumed usage profiles (base fill %/hour). Replace with sensor history when real bins report.
ZONES = {"residential": 4.5, "dining": 7.0, "academic": 3.0, "retail": 6.0, "sports": 2.0}
PEAKS = {
    "dining": (8, 13, 20),
    "residential": (7, 22),
    "retail": (12, 18),
    "academic": (10, 15),
    "sports": (6, 17),
}

HWY = "motorway|trunk|primary|secondary|tertiary|unclassified|residential|service|living_street|road"
MIRRORS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.private.coffee/api/interpreter",
]


def hav_km(a, b):
    """Great-circle distance in km between two (lat, lon) points."""
    p1, p2 = math.radians(a[0]), math.radians(b[0])
    dl = math.radians(b[1] - a[1])
    h = math.sin((p2 - p1) / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 12742 * math.asin(math.sqrt(h))


# =====================================================================
# KML  ->  30 campus bins
# =====================================================================
def read_placemarks():
    """Return every Point placemark as {folder, name, lat, lon}."""
    if os.path.exists(os.path.join(BASE, "data", "campus.kmz")):
        z = zipfile.ZipFile(os.path.join(BASE, "data", "campus.kmz"))
        root = ET.fromstring(z.read(next(n for n in z.namelist() if n.endswith(".kml"))))
    else:
        root = ET.parse(os.path.join(BASE, "data", "campus.kml")).getroot()

    folder_of = {}                                   # placemark -> name of the KML folder it sits in
    for f in root.iter():
        if f.tag.endswith("Folder"):
            fname = (next((c.text for c in f if c.tag.endswith("name")), "") or "").strip()
            for pm in f:
                if pm.tag.endswith("Placemark"):
                    folder_of[id(pm)] = fname

    out = []
    for pm in root.iter():
        if not pm.tag.endswith("Placemark"):
            continue
        point = next((e for e in pm.iter() if e.tag.endswith("Point")), None)
        if point is None:
            continue
        name = (next((c.text for c in pm if c.tag.endswith("name")), "") or "?").strip()
        coords = next(e.text for e in point.iter() if e.tag.endswith("coordinates"))
        lon, lat = (float(v) for v in coords.strip().split(",")[:2])
        out.append(dict(folder=folder_of.get(id(pm), ""), name=name, lat=lat, lon=lon))
    return out


def in_campus(p):
    south, west, north, east = CAMPUS_BOX
    return south <= p["lat"] <= north and west <= p["lon"] <= east


def select_bins(places):
    """Pick N_BINS campus points: de-duplicate, keep the 'Dustbin' folder, spread the rest evenly."""
    depot = next((p for p in places if "depot" in p["name"].lower()), None)

    cand = []                                        # inside the campus box, duplicates removed
    for p in places:
        if "depot" in p["name"].lower() or not in_campus(p):
            continue
        too_close = any(
            hav_km((p["lat"], p["lon"]), (q["lat"], q["lon"])) * 1000 <= DEDUPE_M for q in cand
        )
        if not too_close:
            cand.append(p)

    keep = [p for p in cand if MUST_KEEP_FOLDER in p["folder"].lower()][:N_BINS]
    rest = [p for p in cand if p not in keep]

    while len(keep) < N_BINS and rest:               # farthest-point sampling -> even coverage
        def gap(r):
            return min(hav_km((r["lat"], r["lon"]), (k["lat"], k["lon"])) for k in keep) if keep else 0
        nxt = max(rest, key=gap)
        keep.append(nxt)
        rest.remove(nxt)
    return keep, depot, len(cand)


PLACES = read_placemarks()
RAW_BINS, DEPOT_PM, N_CANDIDATES = select_bins(PLACES)

# Sort bins around the centre so neighbouring bins share a usage profile.
_cx = sum(p["lat"] for p in RAW_BINS) / len(RAW_BINS)
_cy = sum(p["lon"] for p in RAW_BINS) / len(RAW_BINS)
RAW_BINS.sort(key=lambda p: math.atan2(p["lat"] - _cx, p["lon"] - _cy))
for i, p in enumerate(RAW_BINS):
    p["zone"] = list(ZONES)[i * len(ZONES) // len(RAW_BINS)]


# =====================================================================
# ROAD NETWORK (OpenStreetMap)
# =====================================================================
G = None
NODE_XY = {}
ROUTING = "straight-line fallback (road data not loaded)"


def fetch_roads(s, w, n, e):
    """Download drivable roads for the bounding box from the Overpass API."""
    query = f'[out:json][timeout:90];way["highway"~"^({HWY})$"]({s},{w},{n},{e});(._;>;);out body;'
    for url in MIRRORS:
        try:
            print("Downloading campus roads from", url)
            req = urllib.request.Request(
                url,
                data=urllib.parse.urlencode({"data": query}).encode(),
                headers={"User-Agent": "CampusBin/1.0"},
            )
            return json.load(urllib.request.urlopen(req, timeout=120))
        except Exception as ex:
            print("  failed:", ex)
    return None


def build_graph(data):
    """Directed road graph (respects one-way streets) restricted to its drivable core."""
    nodes = {e["id"]: (e["lat"], e["lon"]) for e in data["elements"] if e["type"] == "node"}
    g = nx.DiGraph()
    for e in data["elements"]:
        if e["type"] != "way":
            continue
        tags = e.get("tags", {})
        one_way = tags.get("oneway") in ("yes", "true", "1") or tags.get("junction") == "roundabout"
        reverse = tags.get("oneway") == "-1"
        for a, b in zip(e["nodes"], e["nodes"][1:]):
            if a not in nodes or b not in nodes:
                continue
            d = hav_km(nodes[a], nodes[b])
            if reverse:
                g.add_edge(b, a, length=d)
            else:
                g.add_edge(a, b, length=d)
                if not one_way:
                    g.add_edge(b, a, length=d)
    core = max(nx.strongly_connected_components(g), key=len)
    g = g.subgraph(core).copy()
    return g, {n: nodes[n] for n in g.nodes}


def init_roads(points, tol=0.002):
    """Load roads from the cache if it covers the bins, otherwise download them."""
    global G, NODE_XY, ROUTING
    lat_min, lat_max = min(p[0] for p in points), max(p[0] for p in points)
    lon_min, lon_max = min(p[1] for p in points), max(p[1] for p in points)
    pad = 0.008
    data, cache = None, os.path.join(BASE, "data", "roads.json")

    if os.path.exists(cache):
        try:
            with open(cache, encoding="utf-8") as f:
                c = json.load(f)
            b = c["bbox"]                            # [south, west, north, east]
            if b[0] <= lat_min + tol and b[1] <= lon_min + tol and b[2] >= lat_max - tol and b[3] >= lon_max - tol:
                data = c["data"]
        except (ValueError, KeyError, TypeError, OSError) as ex:   # empty / corrupt cache -> download again
            print("roads.json unreadable (", ex, ") - will download roads again")

    if data is None:
        bbox = [lat_min - pad, lon_min - pad, lat_max + pad, lon_max + pad]
        data = fetch_roads(*bbox)
        if data:
            with open(cache, "w", encoding="utf-8") as f:
                json.dump({"bbox": bbox, "data": data}, f, indent=2)

    if data:
        G, NODE_XY = build_graph(data)
        ROUTING = f"OpenStreetMap road network ({G.number_of_nodes()} junctions, {G.number_of_edges()} road segments)"
    else:
        print("!! No road data - using straight-line distance x", ROAD_FACTOR)


def snap(lat, lon):
    """Nearest road junction to a coordinate."""
    if G is None:
        return None
    return min(NODE_XY, key=lambda k: hav_km((lat, lon), NODE_XY[k]))


_SP = {}


def sp(src):
    """Cached Dijkstra from one junction: (distances, paths)."""
    if src not in _SP:
        _SP[src] = nx.single_source_dijkstra(G, src, weight="length")
    return _SP[src]


def dist(a, b):
    """Road distance in km between two bins/depot."""
    if G is None:
        return hav_km((a["lat"], a["lon"]), (b["lat"], b["lon"])) * ROAD_FACTOR
    return 0.0 if a["node"] == b["node"] else sp(a["node"])[0].get(b["node"], 1e9)


def leg(a, b):
    """Polyline (list of [lat, lon]) that follows the roads from a to b."""
    if G is None:
        return [[a["lat"], a["lon"]], [b["lat"], b["lon"]]]
    if a["node"] == b["node"]:
        return [list(NODE_XY[a["node"]])]
    return [list(NODE_XY[n]) for n in sp(a["node"])[1][b["node"]]]


# =====================================================================
# STATE (simulated bins)
# =====================================================================
def load_bins():
    bins = []
    for i, p in enumerate(RAW_BINS):
        zone = p["zone"]
        bins.append(dict(
            id=f"B{i + 1:02d}",
            name=f"Bin {i + 1:02d}",
            src=f'{p["folder"] or "Campus"} / {p["name"]}',   # where it came from in the KML
            lat=p["lat"], lon=p["lon"], zone=zone,
            node=snap(p["lat"], p["lon"]),
            cap=random.choice([120, 240, 240, 360]),        # litres
            fill=random.uniform(10, 90),
            rate=ZONES[zone] * random.uniform(.8, 1.2),     # true fill rate (%/h)
            rate_est=ZONES[zone],                           # learned estimate
            flagged=False, last_collected=None,
            battery=random.randint(60, 100),
        ))
    return bins


_pts = [(p["lat"], p["lon"]) for p in RAW_BINS]
init_roads(_pts)

if DEPOT_LATLON:
    _dl = DEPOT_LATLON
elif DEPOT_PM:
    _dl = (DEPOT_PM["lat"], DEPOT_PM["lon"])
else:
    _dl = (sum(p[0] for p in _pts) / len(_pts), sum(p[1] for p in _pts) / len(_pts))

DEPOT = {"name": "Waste Depot", "lat": _dl[0], "lon": _dl[1], "node": snap(*_dl)}
if G is not None:                                    # put the depot on a road
    DEPOT["lat"], DEPOT["lon"] = NODE_XY[DEPOT["node"]]

BINS = load_bins()
REPORTS = []
STATE = {"t": time.time(), "sim_hour": 8.0}


def hour_mult(zone, h):
    """Time-of-day multiplier for a zone's fill rate (0.6x off-peak up to 2.2x at peak)."""
    return 0.6 + 1.6 * max(math.exp(-((h % 24 - p) ** 2) / 4) for p in PEAKS[zone])


def tick():
    """Advance the simulated clock and fill the bins."""
    with LOCK:
        now = time.time()
        dt = (now - STATE["t"]) * SIM_SPEED / 3600           # simulated hours elapsed
        STATE["t"] = now
        STATE["sim_hour"] = (STATE["sim_hour"] + dt) % 24
        for b in BINS:
            inst = b["rate"] * hour_mult(b["zone"], STATE["sim_hour"])
            b["fill"] = min(100, b["fill"] + inst * dt)
            b["rate_est"] = 0.9 * b["rate_est"] + 0.1 * inst  # EWMA fill-rate predictor
            b["battery"] = max(5, b["battery"] - dt * 0.002)


# =====================================================================
# ROUTING: capacity-limited VRP = sweep -> nearest neighbour -> 2-opt (road distance)
# =====================================================================
def tour_len(seq, D):
    return sum(D(seq[i], seq[i + 1]) for i in range(len(seq) - 1))


def two_opt(seq, D):
    """Improve a tour by reversing segments while that shortens it."""
    best, cur, improved = seq[:], tour_len(seq, D), True
    while improved:
        improved = False
        for i in range(1, len(best) - 2):
            for j in range(i + 1, len(best) - 1):
                new = best[:i] + best[i:j + 1][::-1] + best[j + 1:]
                length = tour_len(new, D)
                if length + 1e-9 < cur:
                    best, cur, improved = new, length, True
    return best


def vrp(selected, cap=TRUCK_CAP_L):
    """Split bins into truck-sized trips, then order each trip and trace it along the roads."""
    # 1) sweep: sort by angle around the depot and start a new trip when the truck is full
    sel = sorted(selected, key=lambda b: math.atan2(b["lat"] - DEPOT["lat"], b["lon"] - DEPOT["lon"]))
    trips, cur, load = [], [], 0
    for b in sel:
        litres = b["cap"] * b["fill"] / 100
        if cur and load + litres > cap:
            trips.append(cur)
            cur, load = [], 0
        cur.append(b)
        load += litres
    if cur:
        trips.append(cur)

    out = []
    for trip in trips:
        P = [DEPOT] + trip
        D = lambda i, j: dist(P[i], P[j])

        # 2) nearest neighbour
        left, seq = list(range(1, len(P))), [0]
        while left:
            nxt = min(left, key=lambda j: D(seq[-1], j))
            seq.append(nxt)
            left.remove(nxt)

        # 3) 2-opt on the closed tour depot -> bins -> depot
        seq = two_opt(seq + [0], D)

        # 4) build the road polyline and the stop manifest
        path, stops, t = [], [], 0.0
        for i in range(len(seq) - 1):
            seg = leg(P[seq[i]], P[seq[i + 1]])
            path += seg if not path else seg[1:]
            d = D(seq[i], seq[i + 1])
            t += d / TRUCK_KMH * 60
            if i + 1 < len(seq) - 1:                         # arriving at a bin (not back at the depot)
                b = P[seq[i + 1]]
                t += STOP_MIN
                stops.append(dict(id=b["id"], name=b["name"], zone=b["zone"], fill=round(b["fill"]),
                                  leg_km=round(d, 2), eta_min=round(t), flagged=b["flagged"]))

        out.append(dict(
            stops=stops,
            ids=[s["id"] for s in stops],
            path=path,
            km=round(tour_len(seq, D), 2),
            duration_min=round(t),
            load_l=round(sum(b["cap"] * b["fill"] / 100 for b in trip)),
        ))
    return out


def metrics(trips):
    km = sum(t["km"] for t in trips)
    fuel = km * FUEL_L_PER_KM
    return dict(
        km=round(km, 2),
        fuel_l=round(fuel, 2),
        co2_kg=round(fuel * CO2_KG_PER_L, 2),
        trips=len(trips),
        stops=sum(len(t["stops"]) for t in trips),
        duration_min=sum(t["duration_min"] for t in trips),
    )


# =====================================================================
# API
# =====================================================================
@app.get("/api/bins")
def bins():
    tick()
    with LOCK:
        for b in BINS:
            b["tte_h"] = round((100 - b["fill"]) / b["rate_est"], 1) if b["rate_est"] > 0 else None
        zones = {}
        for z in ZONES:
            in_zone = [b for b in BINS if b["zone"] == z]
            zones[z] = round(sum(b["fill"] for b in in_zone) / max(1, len(in_zone)))
        return jsonify(
            bins=BINS, depot=DEPOT, routing=ROUTING, sim_hour=round(STATE["sim_hour"], 2),
            reports=REPORTS[-20:], zones=zones,
            source=dict(candidates=N_CANDIDATES, used=len(BINS), box=CAMPUS_BOX),
        )


@app.get("/api/plan")
def plan():
    tick()
    th = float(request.args.get("threshold", 70))
    hor = float(request.args.get("horizon", 3))
    cap = float(request.args.get("cap", TRUCK_CAP_L))
    with LOCK:
        # visit a bin if it is full enough, predicted full soon, or reported by a citizen
        sel = [b for b in BINS if b["fill"] >= th or b["flagged"] or b["fill"] + b["rate_est"] * hor >= 100]
        opt = vrp(sel, cap)
        base = vrp(BINS, cap)                          # baseline = fixed route visiting every bin
    mo, mb = metrics(opt), metrics(base)
    sav = dict(
        km=round(mb["km"] - mo["km"], 2),
        fuel_l=round(mb["fuel_l"] - mo["fuel_l"], 2),
        co2_kg=round(mb["co2_kg"] - mo["co2_kg"], 2),
        min=mb["duration_min"] - mo["duration_min"],
        pct=round(100 * (1 - mo["km"] / mb["km"]), 1) if mb["km"] else 0,
    )
    return jsonify(routing=ROUTING, trips=opt, optimized=mo, baseline=mb, savings=sav,
                   selected=[b["id"] for b in sel])


@app.get("/api/forecast")
def forecast():
    """Next 24 h with no collection: fill rate per zone, and bins crossing 70 % / overflowing."""
    tick()
    with LOCK:
        h0 = STATE["sim_hour"]
        fill = {b["id"]: b["fill"] for b in BINS}
        hours, zone_rate, over70, full = [], {z: [] for z in ZONES}, [], []
        for k in range(1, 25):
            h = h0 + k
            for z in ZONES:
                in_zone = [b for b in BINS if b["zone"] == z]
                avg = sum(b["rate"] * hour_mult(z, h) for b in in_zone) / max(1, len(in_zone))
                zone_rate[z].append(round(avg, 2))
            for b in BINS:
                fill[b["id"]] = min(100, fill[b["id"]] + b["rate"] * hour_mult(b["zone"], h))
            hours.append(f"{int(h % 24):02d}:00")
            over70.append(sum(v >= 70 for v in fill.values()))
            full.append(sum(v >= 100 for v in fill.values()))
    return jsonify(hours=hours, zone_rate=zone_rate, over70=over70, full=full)


@app.post("/api/collect")
def collect():
    ids = set((request.get_json(silent=True) or {}).get("ids", []))
    with LOCK:
        for b in BINS:
            if b["id"] in ids:
                b.update(fill=random.uniform(0, 5), flagged=False, last_collected=time.strftime("%H:%M:%S"))
    return jsonify(ok=True, collected=len(ids))


@app.post("/api/report")
def report():
    j = request.get_json(silent=True) or {}
    with LOCK:
        b = next((x for x in BINS if x["id"] == j.get("bin_id")), None)
        if not b:
            return jsonify(error="unknown bin"), 404
        b["flagged"] = True
        REPORTS.append(dict(bin_id=b["id"], name=b["name"], type=j.get("type", "overflow"),
                            note=j.get("note", ""), at=time.strftime("%H:%M:%S")))
    return jsonify(ok=True)


@app.post("/api/telemetry")        # IoT hook: ESP32 + ultrasonic sensor POSTs {"bin_id": "B05", "fill": 83.5}
def telemetry():
    j = request.get_json(silent=True) or {}
    with LOCK:
        b = next((x for x in BINS if x["id"] == j.get("bin_id")), None)
        if b:
            b["fill"] = max(0.0, min(100.0, float(j["fill"])))
    return jsonify(ok=bool(b))


@app.post("/api/reset")
def reset():
    global BINS, REPORTS
    with LOCK:
        BINS, REPORTS = load_bins(), []
    return jsonify(ok=True)


@app.get("/")
def index():
    return send_from_directory("static", "index.html")


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)), debug=False)
