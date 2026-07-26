#!/usr/bin/env python3

from curl_cffi import requests as cffi_requests
import requests as stdlib_requests
import re, urllib.parse, hashlib, random, traceback, uuid, json, time, base64, math, io, struct
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import deque
from Crypto.Cipher import AES
from Crypto.Util import Counter
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.backends import default_backend
import numpy as np
from PIL import Image

__version__ = "1.2.0"

CHROME_VERSIONS = [120, 123, 124, 131, 136, 142]
IMPERSONATE_MAP = {
    120: "chrome120", 123: "chrome123", 124: "chrome124",
    131: "chrome131", 136: "chrome136", 142: "chrome142",
}
SCREEN_RESOLUTIONS = [
    "1920x1080", "1366x768", "1536x864", "1440x900", "1280x720",
    "1600x900", "2560x1440", "1920x1200",
]
PLATFORMS = {
    "Windows": {
        "ua":  "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
        "nav": "Win32",
        "sec": '"Windows"',
    },
    "Linux": {
        "ua":  "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
        "nav": "Linux x86_64",
        "sec": '"Linux"',
    },
    "macOS": {
        "ua":  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/{v}.0.0.0 Safari/537.36",
        "nav": "MacIntel",
        "sec": '"macOS"',
    },
}
LANGUAGES = [
    "en-US,en;q=0.9",
    "en-GB,en;q=0.8",
    "en-US,en;q=0.9,es;q=0.7",
]

def lzw_decode(data, min_size, pixel_count):
    clear_code = 1 << min_size
    eoi = clear_code + 1
    code_size = min_size + 1
    code_mask = (1 << code_size) - 1
    dict_table = [[i] for i in range(clear_code)] + [[clear_code], [eoi]]
    next_code = eoi + 1
    output = []
    bits = 0
    bit_buf = 0
    data_pos = 0
    prev = None
    while len(output) < pixel_count:
        while bits < code_size and data_pos < len(data):
            bit_buf |= data[data_pos] << bits
            bits += 8
            data_pos += 1
        code = bit_buf & code_mask
        bit_buf >>= code_size
        bits -= code_size
        if code == clear_code:
            dict_table = [[i] for i in range(clear_code)] + [[clear_code], [eoi]]
            next_code = eoi + 1
            code_size = min_size + 1
            code_mask = (1 << code_size) - 1
            prev = None
        elif code == eoi:
            break
        else:
            if code < len(dict_table):
                entry = dict_table[code]
            elif code == next_code and prev:
                entry = prev + [prev[0]]
            else:
                break
            output.extend(entry)
            if prev and next_code < 4096:
                dict_table.append(prev + [entry[0]])
                next_code += 1
                if next_code > code_mask and code_size < 12:
                    code_size += 1
                    code_mask = (1 << code_size) - 1
            prev = entry
    return output[:pixel_count]


def parse_gif(data):
    pos = 6
    cw = data[pos] | (data[pos+1] << 8)
    ch = data[pos+2] | (data[pos+3] << 8)
    packed = data[pos+4]
    has_gct = (packed >> 7) & 1
    gct_size = 3 * (2 ** ((packed & 0x7) + 1))
    pos += 7
    gct = data[pos:pos+gct_size] if has_gct else None
    if has_gct:
        pos += gct_size
    frames = []
    delay = 0
    transparent_index = -1
    while pos < len(data):
        block = data[pos]
        pos += 1
        if block == 0x3B:
            break
        elif block == 0x21:
            label = data[pos]
            pos += 1
            if label == 0xF9:
                pos += 1
                flags = data[pos]
                delay = (data[pos+1] | (data[pos+2] << 8)) * 10
                pos += 2
                transparent_index = data[pos] if (flags & 1) else -1
                pos += 2
            else:
                while True:
                    sz = data[pos]
                    pos += 1
                    if not sz:
                        break
                    pos += sz
        elif block == 0x2C:
            fx = data[pos] | (data[pos+1] << 8)
            fy = data[pos+2] | (data[pos+3] << 8)
            fw = data[pos+4] | (data[pos+5] << 8)
            fh = data[pos+6] | (data[pos+7] << 8)
            ipacked = data[pos+8]
            pos += 9
            has_lct = (ipacked >> 7) & 1
            lct_size = 3 * (2 ** ((ipacked & 0x7) + 1)) if has_lct else 0
            ct = data[pos:pos+lct_size] if has_lct else gct
            if has_lct:
                pos += lct_size
            min_code = data[pos]
            pos += 1
            lzw_data = []
            while True:
                sz = data[pos]
                pos += 1
                if not sz:
                    break
                lzw_data.extend(data[pos:pos+sz])
                pos += sz
            pixels = lzw_decode(lzw_data, min_code, fw * fh)
            patch = np.zeros((fh, fw, 4), dtype=np.uint8)
            for i, ci in enumerate(pixels):
                ci3 = ci * 3
                if ci3 + 2 < len(ct):
                    patch[i // fw, i % fw] = [ct[ci3], ct[ci3+1], ct[ci3+2], 0 if ci == transparent_index else 255]
            frames.append({'x': fx, 'y': fy, 'w': fw, 'h': fh, 'delay': delay, 'patch': patch})
    return {'w': cw, 'h': ch, 'frames': frames}


def composite_frames(gif):
    w, h = gif['w'], gif['h']
    canvas = np.zeros((h, w, 4), dtype=np.uint8)
    composed = []
    for frame in gif['frames']:
        next_canvas = canvas.copy()
        fx0, fy0, fw, fh = frame['x'], frame['y'], frame['w'], frame['h']
        cy1, cy2 = fy0, min(fy0 + fh, h)
        cx1, cx2 = fx0, min(fx0 + fw, w)
        if cy2 > cy1 and cx2 > cx1:
            src  = frame['patch'][:cy2-cy1, :cx2-cx1]
            mask = src[:, :, 3] > 0
            dst  = next_canvas[cy1:cy2, cx1:cx2]
            dst[mask] = src[mask]
        composed.append(next_canvas)
        canvas = next_canvas
    return composed

def _extract_frames_fast(data):
    """Pillow C-decoder replacement for parse_gif+composite_frames (~4-10x faster)."""
    img = Image.open(io.BytesIO(bytes(data)))
    w, h = img.size
    canvas = np.zeros((h, w, 4), dtype=np.uint8)
    composed = []
    try:
        while True:
            tile = img.tile
            if tile:
                fx, fy = tile[0][1][0], tile[0][1][1]
                fw = tile[0][1][2] - fx
                fh = tile[0][1][3] - fy
            else:
                fx, fy, fw, fh = 0, 0, w, h
            patch = np.array(img.convert("RGBA"), dtype=np.uint8)
            next_canvas = canvas.copy()
            next_canvas[fy:fy+fh, fx:fx+fw] = patch[fy:fy+fh, fx:fx+fw]
            composed.append(next_canvas)
            canvas = next_canvas
            img.seek(img.tell() + 1)
    except EOFError:
        pass
    return w, h, composed

def detect_bg(rgba, w, h):
    C = 12
    samples = []
    for y in range(min(C, h)):
        for x in range(min(C, w)):
            for px, py in [(x, y), (w-1-x, y), (x, h-1-y), (w-1-x, h-1-y)]:
                if 0 <= px < w and 0 <= py < h:
                    samples.append(rgba[py, px, :3])
    samples = np.array(samples)
    return {
        'bgR': int(np.median(samples[:, 0])),
        'bgG': int(np.median(samples[:, 1])),
        'bgB': int(np.median(samples[:, 2])),
    }


def saturation(r, g, b):
    rn, gn, bn = r/255, g/255, b/255
    max_c = max(rn, gn, bn)
    min_c = min(rn, gn, bn)
    l = (max_c + min_c) / 2
    if max_c == min_c:
        return 0
    d = max_c - min_c
    return d / (2 - max_c - min_c if l > 0.5 else max_c + min_c)


def find_blobs(rgba, w, h, bgR, bgG, bgB, thresh=22, min_size=12, min_sat=0):
    # build a foreground mask in one shot instead of checking every pixel in Python
    fg = ((np.abs(rgba[:, :, 0].astype(np.int16) - bgR) +
           np.abs(rgba[:, :, 1].astype(np.int16) - bgG) +
           np.abs(rgba[:, :, 2].astype(np.int16) - bgB)) > thresh)
    visited = np.zeros((h, w), dtype=bool)
    blobs = []
    # only BFS from pixels we know are foreground
    ys, xs = np.where(fg)
    for y, x in zip(ys.tolist(), xs.tolist()):
        if visited[y, x]:
            continue
        queue = deque([(x, y)])
        pixels = []
        visited[y, x] = True
        ri = gi = bi = 0
        while queue:
            cx, cy = queue.popleft()
            pixels.append((cx, cy))
            ri += int(rgba[cy, cx, 0])
            gi += int(rgba[cy, cx, 1])
            bi += int(rgba[cy, cx, 2])
            for nx, ny in ((cx-1, cy), (cx+1, cy), (cx, cy-1), (cx, cy+1)):
                if 0 <= nx < w and 0 <= ny < h and not visited[ny, nx] and fg[ny, nx]:
                    visited[ny, nx] = True
                    queue.append((nx, ny))
        if len(pixels) < min_size:
            continue
        n = len(pixels)
        cx_mean = sum(p[0] for p in pixels) / n
        cy_mean = sum(p[1] for p in pixels) / n
        mr, mg, mb = ri / n, gi / n, bi / n
        sat = saturation(mr, mg, mb)
        if sat < min_sat:
            continue
        blobs.append({'cx': cx_mean, 'cy': cy_mean, 'size': n, 'r': mr, 'g': mg, 'b': mb, 'sat': sat})
    return sorted(blobs, key=lambda b: b['size'], reverse=True)


def detect_sat_threshold(rgba, w, h, bgR, bgG, bgB):
    all_blobs = find_blobs(rgba, w, h, bgR, bgG, bgB, 22, 4, 0)
    if len(all_blobs) < 3:
        return 0
    sats = sorted(b['sat'] for b in all_blobs)
    max_gap, gap_at = 0, 0
    for i in range(1, len(sats)):
        gap = sats[i] - sats[i-1]
        if gap > max_gap:
            max_gap = gap
            gap_at = sats[i-1]
    threshold = (gap_at + max_gap * 0.5) if max_gap > 0.10 else 0
    n_above = sum(1 for s in sats if s > threshold)
    return threshold if (threshold > 0 and n_above >= 3) else 0


def track_blobs(composed, w, h, bgR, bgG, bgB, seeds, thresh=22, min_size=10, max_dist=60, min_sat=0):
    tracks = [[{'cx': b['cx'], 'cy': b['cy'], 'r': b['r'], 'g': b['g'], 'b': b['b'], 'sat': b['sat']}] for b in seeds]
    for fi in range(1, len(composed)):
        frame_blobs = find_blobs(composed[fi], w, h, bgR, bgG, bgB, thresh, min_size, min_sat)
        pairs = []
        for ai, track in enumerate(tracks):
            valid = [p for p in track if p is not None]
            if not valid:
                continue
            last = valid[-1]
            pred_cx, pred_cy = last['cx'], last['cy']
            if len(valid) >= 2:
                prev = valid[-2]
                pred_cx = last['cx'] + (last['cx'] - prev['cx'])
                pred_cy = last['cy'] + (last['cy'] - prev['cy'])
            for bi, fb in enumerate(frame_blobs):
                if math.hypot(fb['cx'] - last['cx'], fb['cy'] - last['cy']) >= max_dist:
                    continue
                sp_pred = math.hypot(fb['cx'] - pred_cx, fb['cy'] - pred_cy)
                cd = math.sqrt((fb['r']-last['r'])**2 + (fb['g']-last['g'])**2 + (fb['b']-last['b'])**2)
                pairs.append({'score': sp_pred + cd * 0.25, 'ai': ai, 'bi': bi, 'fb': fb})
        pairs.sort(key=lambda p: p['score'])
        used_a, used_b, asgn = set(), set(), {}
        for p in pairs:
            if p['ai'] in used_a or p['bi'] in used_b:
                continue
            used_a.add(p['ai'])
            used_b.add(p['bi'])
            asgn[p['ai']] = p['fb']
        for ai in range(len(tracks)):
            tracks[ai].append(asgn.get(ai))
    return tracks

def fit_circle(pts):
    n = len(pts)
    if n < 4:
        return None
    mx = sum(p[0] for p in pts) / n
    my = sum(p[1] for p in pts) / n
    u = [[p[0]-mx, p[1]-my] for p in pts]
    suu = sum(ux*ux for ux, uy in u)
    svv = sum(uy*uy for ux, uy in u)
    suv = sum(ux*uy for ux, uy in u)
    suuu = sum(ux**3 for ux, uy in u)
    svvv = sum(uy**3 for ux, uy in u)
    suvv = sum(ux*uy*uy for ux, uy in u)
    svuu = sum(uy*ux*ux for ux, uy in u)
    r1 = 0.5 * (suuu + suvv)
    r2 = 0.5 * (svvv + svuu)
    det = suu * svv - suv * suv
    if abs(det) < 1e-8:
        return None
    uc = (r1 * svv - r2 * suv) / det
    vc = (r2 * suu - r1 * suv) / det
    radius = math.sqrt(uc*uc + vc*vc + (suu + svv) / n)
    if not math.isfinite(radius) or radius < 1 or radius > 3000:
        return None
    return {'cx': uc + mx, 'cy': vc + my, 'r': radius}


def unwrap_angles(angles):
    if not angles:
        return []
    out = [angles[0]]
    for i in range(1, len(angles)):
        d = angles[i] - out[-1]
        while d > math.pi:
            d -= 2 * math.pi
        while d < -math.pi:
            d += 2 * math.pi
        out.append(out[-1] + d)
    return out


def lin_reg(xs, ys):
    n = len(xs)
    if n < 3:
        return {'slope': 0, 'r2': 0}
    mx = sum(xs) / n
    my = sum(ys) / n
    sxx = sum((x-mx)**2 for x in xs)
    sxy = sum((xs[i]-mx) * (ys[i]-my) for i in range(n))
    syy = sum((y-my)**2 for y in ys)
    if sxx < 1e-12:
        return {'slope': 0, 'r2': 0}
    slope = sxy / sxx
    ss_res = sum((ys[i] - (slope * xs[i] + my - slope * mx))**2 for i in range(n))
    r2 = max(0, 1 - ss_res/syy if syy > 1e-12 else 1)
    return {'slope': slope, 'r2': r2}


def shoelace_dir(pts):
    n = len(pts)
    if n < 4:
        return None
    mx = sum(p[0] for p in pts) / n
    my = sum(p[1] for p in pts) / n
    pos, neg = 0, 0
    for i in range(1, n):
        ax, ay = pts[i-1][0] - mx, pts[i-1][1] - my
        bx, by = pts[i][0] - mx, pts[i][1] - my
        cross = ax * by - ay * bx
        if cross > 0:
            pos += cross
        else:
            neg -= cross
    total = pos + neg
    if total < 1e-6:
        return None
    return {'dir': 'CCW' if pos > neg else 'CW', 'dominance': max(pos, neg) / total}

def solve_driftodd(gif, composed):
    w, h = gif['w'], gif['h']
    bg = detect_bg(composed[0], w, h)
    bgR, bgG, bgB = bg['bgR'], bg['bgG'], bg['bgB']
    n_frames = len(composed)
    sat_thresh = detect_sat_threshold(composed[0], w, h, bgR, bgG, bgB)

    seeds = None
    for min_sz in [8, 15, 30, 50, 80]:
        blobs = find_blobs(composed[0], w, h, bgR, bgG, bgB, 22, min_sz, sat_thresh)
        if 3 <= len(blobs) <= 20:
            seeds = blobs[:14]
            break
    if not seeds or len(seeds) < 3:
        for fi in range(1, min(n_frames, 6)):
            for min_sz in [8, 15, 30]:
                blobs = find_blobs(composed[fi], w, h, bgR, bgG, bgB, 22, min_sz, sat_thresh)
                if 3 <= len(blobs) <= 20 and len(blobs) > len(seeds or []):
                    seeds = blobs[:14]
    if not seeds or len(seeds) < 2:
        return {'answer': None, 'reason': 'no seeds'}

    seeds = seeds[:10]
    tracks = track_blobs(composed, w, h, bgR, bgG, bgB, seeds, 22, 8, 60, sat_thresh)

    classified = []
    for ti, track in enumerate(tracks):
        valid = [(i, p) for i, p in enumerate(track) if p is not None]
        if len(valid) < max(4, n_frames * 0.25):
            continue
        pts = [p for _, p in valid]
        xy_pts = [[p['cx'], p['cy']] for p in pts]
        circ = fit_circle(xy_pts)
        mean_cx = sum(p[0] for p in xy_pts) / len(xy_pts)
        mean_cy = sum(p[1] for p in xy_pts) / len(xy_pts)
        orbit_cx = circ['cx'] if circ else mean_cx
        orbit_cy = circ['cy'] if circ else mean_cy
        max_disp = max(math.hypot(p[0]-xy_pts[0][0], p[1]-xy_pts[0][1]) for p in xy_pts)
        if (circ and circ['r'] < 5 or not circ) and max_disp < 8:
            continue
        frame_idxs = [i for i, _ in valid]
        raw_angles = [math.atan2(p['cy']-orbit_cy, p['cx']-orbit_cx) for p in pts]
        unwrapped = unwrap_angles(raw_angles)
        reg = lin_reg(frame_idxs, unwrapped)
        dir_result = None
        confidence = 0
        if abs(reg['slope']) > 0.005 and reg['r2'] > 0.45:
            dir_result = 'CCW' if reg['slope'] > 0 else 'CW'
            confidence = reg['r2']
        else:
            vote = shoelace_dir(xy_pts)
            if vote and vote['dominance'] > 0.75:
                dir_result = vote['dir']
                confidence = vote['dominance'] * 0.5
        if not dir_result:
            continue
        classified.append({
            'ti': ti, 'dir': dir_result, 'confidence': confidence, 'r2': reg['r2'],
            'validFrames': len(valid), 'clickCx': seeds[ti]['cx'], 'clickCy': seeds[ti]['cy']
        })

    if len(classified) < 2:
        return {'answer': None, 'reason': f'only {len(classified)} classified'}

    cw = [c for c in classified if c['dir'] == 'CW']
    ccw = [c for c in classified if c['dir'] == 'CCW']

    if not cw or not ccw:
        present_dir = 'CW' if cw else 'CCW'
        opposite_dir = 'CCW' if present_dir == 'CW' else 'CW'
        in_set = set(c['ti'] for c in classified)
        for ti, track in enumerate(tracks):
            if ti in in_set:
                continue
            valid = [(i, p) for i, p in enumerate(track) if p is not None]
            if len(valid) < 4:
                continue
            xy_pts = [[p['cx'], p['cy']] for _, p in valid]
            max_disp = max(math.hypot(p[0]-xy_pts[0][0], p[1]-xy_pts[0][1]) for p in xy_pts)
            if max_disp < 8:
                continue
            vote = shoelace_dir(xy_pts)
            if not vote or vote['dominance'] < 0.80 or vote['dir'] != opposite_dir:
                continue
            classified.append({'ti': ti, 'dir': opposite_dir, 'confidence': vote['dominance']*0.4,
                                'validFrames': len(valid), 'clickCx': seeds[ti]['cx'], 'clickCy': seeds[ti]['cy']})
        cw = [c for c in classified if c['dir'] == 'CW']
        ccw = [c for c in classified if c['dir'] == 'CCW']

    if not cw or not ccw:
        return {'answer': None, 'reason': 'all tracks same direction after recovery'}

    if len(cw) != len(ccw):
        odd = cw if len(cw) < len(ccw) else ccw
    else:
        cw_conf = sum(c['confidence'] for c in cw)
        ccw_conf = sum(c['confidence'] for c in ccw)
        odd = cw if cw_conf <= ccw_conf else ccw

    if len(odd) > 1:
        odd = [sorted(odd, key=lambda x: x['confidence'], reverse=True)[0]]

    best = odd[0]
    return {'answer': {'cx': best['clickCx'], 'cy': best['clickCy']}, 'confidence': round(best['confidence'], 6)}


def solve_coherence(gif, composed):
    w, h = gif['w'], gif['h']
    bg = detect_bg(composed[0], w, h)
    bgR, bgG, bgB = bg['bgR'], bg['bgG'], bg['bgB']
    cell = max(20, min(35, round(math.sqrt(w*h)/14)))

    attempts = [
        {'THRESH': 18, 'MIN_SIZE': 4, 'MAX_MATCH': 22, 'minDots': 5},
        {'THRESH': 18, 'MIN_SIZE': 3, 'MAX_MATCH': 35, 'minDots': 3},
        {'THRESH': 22, 'MIN_SIZE': 2, 'MAX_MATCH': 50, 'minDots': 2},
        {'THRESH': 26, 'MIN_SIZE': 2, 'MAX_MATCH': 70, 'minDots': 2},
    ]

    all_vecs, dot_frames = None, None
    for attempt in attempts:
        dot_frames_try = []
        for rgba in composed:
            blobs = find_blobs(rgba, w, h, bgR, bgG, bgB,
                               attempt['THRESH'], attempt['MIN_SIZE'], 0)
            dot_frames_try.append([[b['cx'], b['cy']] for b in blobs])

        # match each dot to its closest neighbour in the next frame
        all_vecs_try = []
        for step in [1, 2]:
            weight = 1.0 if step == 1 else 0.6
            match_radius = attempt['MAX_MATCH'] * (1.6 if step == 2 else 1)
            mr_sq = match_radius * match_radius
            for fi in range(len(dot_frames_try) - step):
                p0r = dot_frames_try[fi]
                p1r = dot_frames_try[fi + step]
                if len(p0r) < attempt['minDots'] or len(p1r) < attempt['minDots']:
                    continue
                p0n = np.array(p0r, dtype=np.float32)   # (m, 2)
                p1n = np.array(p1r, dtype=np.float32)   # (n, 2)
                # All pairwise squared distances in one shot: (m, n)
                diff = p1n[np.newaxis, :, :] - p0n[:, np.newaxis, :]
                dist_sq = diff[:, :, 0] ** 2 + diff[:, :, 1] ** 2
                best_j = np.argmin(dist_sq, axis=1)           # (m,)
                best_dsq = dist_sq[np.arange(len(p0n)), best_j]
                for i in np.where(best_dsq < mr_sq)[0]:
                    dx0, dy0 = p0r[i]
                    j = int(best_j[i])
                    vx = (p1r[j][0] - dx0) / step
                    vy = (p1r[j][1] - dy0) / step
                    if vx * vx + vy * vy < 0.25:
                        continue
                    all_vecs_try.append([dx0, dy0, vx, vy, weight])

        if len(all_vecs_try) >= 20:
            all_vecs = all_vecs_try
            dot_frames = dot_frames_try
            break
        if not all_vecs or len(all_vecs_try) > len(all_vecs):
            all_vecs = all_vecs_try
            dot_frames = dot_frames_try

    if not all_vecs or len(all_vecs) < 20:
        return {'answer': None, 'reason': 'too few vectors'}

    # score each grid cell by how coherent (same speed + direction) its motion vectors are
    nx, ny = w // cell, h // cell
    av = np.array(all_vecs, dtype=np.float64)       # (N, 5): cx,cy,vx,vy,wgt
    bxs = np.clip((av[:, 0] / cell).astype(int), 0, nx - 1)
    bys = np.clip((av[:, 1] / cell).astype(int), 0, ny - 1)
    angles = np.arctan2(av[:, 3], av[:, 2])
    speeds = np.sqrt(av[:, 2] ** 2 + av[:, 3] ** 2)
    wgts   = av[:, 4]

    cmap = np.zeros((ny, nx), dtype=np.float64)
    for by in range(ny):
        for bx in range(nx):
            mask = (bys == by) & (bxs == bx)
            if mask.sum() < 6:
                continue
            w_m = wgts[mask]
            tot_w = w_m.sum()
            mean_spd = (speeds[mask] * w_m).sum() / tot_w
            sx = (np.sin(angles[mask]) * w_m).sum()
            cx3 = (np.cos(angles[mask]) * w_m).sum()
            cv = 1 - math.sqrt((sx / tot_w) ** 2 + (cx3 / tot_w) ** 2)
            cmap[by, bx] = mean_spd * (1 - cv)

    # smooth the coherence map with a lightweight 3x3 gaussian — no scipy needed
    from numpy.lib.stride_tricks import sliding_window_view
    padded = np.pad(cmap, 1, mode='edge')
    kernel = np.array([[1, 2, 1], [2, 4, 2], [1, 2, 1]], dtype=np.float64)
    wins   = sliding_window_view(padded, (3, 3))      # (ny, nx, 3, 3)
    sm     = (wins * kernel).sum(axis=(-2, -1)) / kernel.sum()
    # Suppress border cells
    border_mask = np.zeros((ny, nx), dtype=bool)
    border_mask[0, :] = border_mask[-1, :] = True
    border_mask[:, 0] = border_mask[:, -1] = True
    sm[border_mask] *= 0.60

    flat_idx = int(np.argmax(sm))
    best_by, best_bx = divmod(flat_idx, nx)
    best_val = float(sm[best_by, best_bx])

    # Dominant flow angle in winning cell
    win_mask = (bys == best_by) & (bxs == best_bx)
    if win_mask.any():
        ww = wgts[win_mask]
        win_angle = math.atan2(
            (np.sin(angles[win_mask]) * ww).sum(),
            (np.cos(angles[win_mask]) * ww).sum()
        )
    else:
        win_angle = 0.0

    # Collect dots from winning cell neighbourhood
    near_dots = []
    for dy in range(-1, 2):
        for dx in range(-1, 2):
            nbx, nby = best_bx + dx, best_by + dy
            if 0 <= nbx < nx and 0 <= nby < ny and sm[nby, nbx] > 0:
                for ddx, ddy in dot_frames[0]:
                    if int(ddx / cell) == nbx and int(ddy / cell) == nby:
                        near_dots.append([ddx, ddy, float(sm[nby, nbx])])

    if near_dots:
        weights = []
        for ddx, ddy, cw2 in near_dots:
            my_vec = next((v for cx2, cy2, vx, vy, wgt in all_vecs
                           if math.hypot(cx2 - ddx, cy2 - ddy) < cell
                           for v in [[math.atan2(vy, vx), math.hypot(vx, vy), wgt]]), None)
            align = 0.5 + 0.5 * math.cos(my_vec[0] - win_angle) if my_vec else 0.5
            weights.append(cw2 * align)
        w_sum = sum(weights) or 1
        click_cx = sum(ddx * wt for (ddx, _, _), wt in zip(near_dots, weights)) / w_sum
        click_cy = sum(ddy * wt for (_, ddy, _), wt in zip(near_dots, weights)) / w_sum
    else:
        click_cx = (best_bx + 0.5) * cell
        click_cy = (best_by + 0.5) * cell

    return {'answer': {'cx': click_cx, 'cy': click_cy}, 'confidence': round(min(1, best_val / 5), 6)}

def _random_fingerprint():
    plat_name = random.choices(
        ["Windows", "macOS", "Linux"],
        weights=[72, 20, 8],
    )[0]
    plat = PLATFORMS[plat_name]
    v = random.choices(
        CHROME_VERSIONS,
        weights=[3, 6, 10, 18, 24, 39],  # oldest → newest
    )[0]
    res = random.choices(
        SCREEN_RESOLUTIONS,
        weights=[35, 20, 15, 10, 8, 6, 4, 2],
    )[0]
    brand_orders = [
        f'"Chromium";v="{v}", "Not:A-Brand";v="24", "Google Chrome";v="{v}"',
        f'"Google Chrome";v="{v}", "Chromium";v="{v}", "Not:A-Brand";v="24"',
    ]
    return {
        "user_agent":         plat["ua"].format(v=v),
        "platform":           plat_name,
        "navigator_platform": plat["nav"],
        "sec_ch_ua":          random.choice(brand_orders),
        "sec_ch_ua_platform": plat["sec"],
        "language":           random.choice(LANGUAGES),
        "resolution":         res,
        "chrome_version":     v,
    }


def _build_session(fp):
    session = cffi_requests.Session(impersonate=IMPERSONATE_MAP[fp["chrome_version"]])
    session.headers.update({
        "User-Agent":                fp["user_agent"],
        "Accept":                    "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7",
        "Accept-Language":           fp["language"],
        "Accept-Encoding":           "gzip, deflate, br, zstd",
        "Connection":                "keep-alive",
        "Sec-CH-UA":                 fp["sec_ch_ua"],
        "Sec-CH-UA-Mobile":          "?0",
        "Sec-CH-UA-Platform":        fp["sec_ch_ua_platform"],
        "Sec-Fetch-Dest":            "document",
        "Sec-Fetch-Mode":            "navigate",
        "Sec-Fetch-Site":            "none",
        "Sec-Fetch-User":            "?1",
        "Upgrade-Insecure-Requests": "1",
    })
    return session


def _get_param(url, param):
    parsed = urllib.parse.urlparse(url)
    params = urllib.parse.parse_qs(parsed.query)
    values = params.get(param, [])
    return values[0] if values else None

def _solve_captcha_once():
    """One captcha attempt. Returns the token string or None."""
    cap_session = None
    try:
        fp = _random_fingerprint()
        cap_session = _build_session(fp)
        cap_session.headers.update({
            "Accept":         "application/json",
            "Sec-Fetch-Dest": "empty",
            "Sec-Fetch-Mode": "cors",
            "Sec-Fetch-Site": "cross-site",
            "Origin":         "https://auth.platorelay.com",
            "Referer":        "https://auth.platorelay.com/",
        })
        cap_session.headers.pop("Upgrade-Insecure-Requests", None)
        cap_session.headers.pop("Sec-Fetch-User", None)

        challenge = cap_session.get("https://captcha.platorelay.com/api/challenge", timeout=10).json()
        chalid    = challenge.get("challenge_id")
        ctype     = challenge.get("type", "")
        img_url   = "https://captcha.platorelay.com" + challenge.get("image", "")

        # reuse the session so we don't open a new TLS connection just for the gif
        cap_session.headers["Accept"] = "image/gif,image/*;q=0.9,*/*;q=0.8"
        buf = cap_session.get(img_url, timeout=15).content
        cap_session.headers["Accept"] = "application/json"

        # Pillow decodes the gif in C — much faster than the old pure-Python loop
        gw, gh, composed = _extract_frames_fast(buf)
        meta = {"w": gw, "h": gh, "frames": []}

        if ctype == "driftodd":
            result = solve_driftodd(meta, composed)
        elif ctype == "coherence":
            result = solve_coherence(meta, composed)
        else:
            result = solve_driftodd(meta, composed)
            if not result.get("answer"):
                result = solve_coherence(meta, composed)

        if not result.get("answer"):
            return None

        x, y = result["answer"]["cx"], result["answer"]["cy"]
        resp = cap_session.post(
            "https://captcha.platorelay.com/api/answer",
            json={"challenge_id": chalid, "x": x, "y": y},
            timeout=10,
        ).json()

        return resp.get("token") if resp.get("success") else None
    except Exception:
        return None
    finally:
        if cap_session:
            try:
                cap_session.close()
            except Exception:
                pass

def solve_captcha():
    """Solve PlatoRelay captcha. Runs 3 workers in parallel and returns the first valid token."""
    for _round in range(14):
        ex = ThreadPoolExecutor(max_workers=3)
        futures = [ex.submit(_solve_captcha_once) for _ in range(3)]
        ex.shutdown(wait=False)  # don't wait — bail out as soon as one succeeds
        for f in as_completed(futures, timeout=30):
            token = f.result()
            if token:
                return token  # got one, bail out early
    return None

def solve_captcha_external():
    """Captcha solver via tirex-delta.vercel.app — single HTTP call per solve."""
    for _ in range(37):
        try:
            resp = stdlib_requests.get(
                "https://tirex-delta.vercel.app/api/solve",
                timeout=15,
            ).json()
            if resp.get("success") and resp.get("token"):
                return resp["token"]
        except Exception:
            pass
    return None

def generate_stream(ticket: str, screen_width=1920, screen_height=1080) -> str:
    """
    Encrypt the browser event stream sent with every step PUT.
    Mirrors the SPA's getStream(): clickBuffer → lastClick → lastMouseMove →
    lastTouchStart (mobile) → snapshot marker (event 5).
    Keys: ticket[1:17] / ticket[17:33] (AES-128-CTR).
    """
    try:
        now       = int(time.time() * 1000)
        is_mobile = random.random() < 0.12
        events    = []

        def ev(typ, x, y, tag, t):
            events.append({"event": typ, "data": {
                "x": int(max(0, min(screen_width,  x))),
                "y": int(max(0, min(screen_height, y))),
                "target": tag, "time": int(t),
            }})

        # 0.44 because checkpoint buttons typically sit slightly above the fold centre
        btn_x = int(screen_width  * 0.50) + random.randint(-70, 70)
        btn_y = int(screen_height * 0.44) + random.randint(-50, 50)

        if is_mobile:
            t = now - random.randint(5000, 14000)
            for _ in range(random.randint(0, 2)):
                t += random.randint(1000, 4000)
                px = random.randint(int(screen_width * 0.15), int(screen_width * 0.85))
                py = random.randint(int(screen_height * 0.15), int(screen_height * 0.75))
                ev(1, px, py, random.choice(["BUTTON", "A", "DIV"]), t)

            t_click = now - random.randint(120, 600)
            ev(1, btn_x + random.randint(-5, 5), btn_y + random.randint(-5, 5), "BUTTON", t_click)

            # touchstart fires before the finger lifts, so its timestamp is earlier
            t_touch = t_click - random.randint(40, 140)
            ev(2, btn_x + random.randint(-8, 8), btn_y + random.randint(-8, 8), "BUTTON", t_touch)

        else:
            cx = random.randint(int(screen_width  * 0.10), int(screen_width  * 0.90))
            cy = random.randint(int(screen_height * 0.10), int(screen_height * 0.75))
            t  = now - random.randint(5000, 14000)

            IDLE_TAGS     = ["BODY", "DIV", "P", "H1", "H2", "SPAN"]
            APPROACH_TAGS = ["DIV", "SPAN", "BUTTON"]

            # user reads the page before moving toward the button
            for _ in range(random.randint(2, 5)):
                t  += random.randint(180, 1400)
                cx  = cx + random.randint(-280, 280)
                cy  = cy + random.randint(-180, 180)
                ev(0, cx, cy, random.choice(IDLE_TAGS), t)

            # cursor converges on the button over 2–4 steps
            n_app = random.randint(2, 4)
            for i in range(n_app):
                t   += random.randint(50, 320)
                frac = (i + 1) / n_app * random.uniform(0.65, 1.0)
                cx   = cx + (btn_x - cx) * frac + random.randint(-6, 6)
                cy   = cy + (btn_y - cy) * frac + random.randint(-6, 6)
                tag  = "BUTTON" if i == n_app - 1 else random.choice(APPROACH_TAGS)
                ev(0, cx, cy, tag, t)

            # clickBuffer drains before lastClick, so earlier clicks come first
            t_prior = now - random.randint(6000, 14000)
            for _ in range(random.randint(0, 3)):
                t_prior += random.randint(600, 2800)
                px = random.randint(int(screen_width  * 0.20), int(screen_width  * 0.80))
                py = random.randint(int(screen_height * 0.20), int(screen_height * 0.70))
                ev(1, px, py, random.choice(["BUTTON", "A", "DIV", "SPAN"]), t_prior)

            t += random.randint(140, 700)  # dwell before clicking
            t_click = t
            ev(1, btn_x + random.randint(-3, 3), btn_y + random.randint(-3, 3), "BUTTON", t_click)

            # lastMouseMove timestamp is just before the click, not after
            t_move = t_click - random.randint(14, 55)
            ev(0, btn_x + random.randint(-6, 6), btn_y + random.randint(-6, 6), "BUTTON", t_move)

        events.append({"event": 5, "data": {"time": now, "length": 0}})

        payload  = json.dumps({"events": events})
        key      = bytes(ord(c) for c in ticket[1:17])
        iv_bytes = bytes(ord(c) for c in ticket[17:33])
        ctr      = Counter.new(128, initial_value=int.from_bytes(iv_bytes, "big"))
        cipher   = AES.new(key, AES.MODE_CTR, counter=ctr)
        return cipher.encrypt(payload.encode("utf-8")).hex()
    except Exception:
        return ""


def getMeta(ticket: str, screen_res: str, user_agent: str, nav_platform: str) -> str:
    """
    Encrypt the browser fingerprint payload sent with every step PUT.
    Keys: ticket[0:16] / ticket[16:32] (AES-128-CTR).
    """
    try:
        if not ticket or len(ticket) < 32:
            return "empty"
        key      = bytes(ord(c) for c in ticket[0:16])
        iv_bytes = bytes(ord(c) for c in ticket[16:32])
        sw, sh   = int(screen_res.split("x")[0]), int(screen_res.split("x")[1])

        # Windows taskbar is 40 px by default, 48 with large icons; Linux panels
        # run ~32 px; macOS only subtracts the 23 px menu bar for a maximised window
        avail_h = sh - random.choices(
            [40, 48, 32, 23],
            weights=[55, 20, 15, 10],
        )[0]

        # Chrome 85+ always exposes exactly these five PDF plugins in this order
        plugins_item = [
            {"name": "PDF Viewer",                "filename": "internal-pdf-viewer", "description": "Portable Document Format"},
            {"name": "Chrome PDF Viewer",         "filename": "internal-pdf-viewer", "description": "Portable Document Format"},
            {"name": "Chromium PDF Viewer",       "filename": "internal-pdf-viewer", "description": "Portable Document Format"},
            {"name": "Microsoft Edge PDF Viewer", "filename": "internal-pdf-viewer", "description": "Portable Document Format"},
            {"name": "WebKit built-in PDF",       "filename": "internal-pdf-viewer", "description": "Portable Document Format"},
        ]
        mimetypes_item = [
            {"type": "application/pdf", "description": "Portable Document Format", "suffixes": "pdf"},
            {"type": "text/pdf",        "description": "Portable Document Format", "suffixes": "pdf"},
        ]

        # Chrome quantises downlink to the nearest 0.25 Mbps and rtt to 25 ms
        conn = random.choices(
            [
                {"effectiveType": "4g", "downlink": 10,   "rtt": 50},
                {"effectiveType": "4g", "downlink": 5,    "rtt": 75},
                {"effectiveType": "4g", "downlink": 2.5,  "rtt": 100},
                {"effectiveType": "4g", "downlink": 1.25, "rtt": 150},
                {"effectiveType": "3g", "downlink": 0.75, "rtt": 300},
                {"effectiveType": "3g", "downlink": 0.5,  "rtt": 375},
            ],
            weights=[40, 22, 16, 10, 8, 4],
        )[0]

        hist_len = random.choices([1, 2, 3, 4], weights=[30, 35, 25, 10])[0]

        info = [
            {"name": "screen", "data": {
                "width":       sw,
                "height":      sh,
                "availWidth":  sw,
                "availHeight": avail_h,
                "colorDepth":  24,
                "pixelDepth":  24,
                "orientation": {"type": "landscape-primary", "angle": 0},
            }},
            {"name": "navigator", "data": {
                "userAgent":      user_agent,
                "platform":       nav_platform,
                "maxTouchPoints": 0,
                "plugins":   {"length": len(plugins_item),   "item": plugins_item},
                "mimeTypes": {"length": len(mimetypes_item), "item": mimetypes_item},
            }},
            {"name": "performance", "data": int(time.time() * 1000)},
            {"name": "history",     "data": {"length": hist_len}},
            {"name": "webdriver",   "webdriver": False},
            {"name": "connection",  "data": {**conn, "saveData": False}},
        ]
        payload = json.dumps({"browserInfo": info}, separators=(",", ":"))
        ctr    = Counter.new(128, initial_value=int.from_bytes(iv_bytes, "big"))
        cipher = AES.new(key, AES.MODE_CTR, counter=ctr)
        return cipher.encrypt(payload.encode("utf-8")).hex()
    except Exception:
        return "empty"


def checkKey(ticket, session):
    # retry once on transient network errors
    for _ in range(2):
        try:
            data = session.get(
                f"https://auth.platorelay.com/api/session/status?ticket={ticket}",
                timeout=10,
            ).json().get("data", {})
            key = data.get("key")
            return None if (not key or key == "KEY_NOT_FOUND") else key
        except Exception:
            time.sleep(0.2)
    return None


def _resolve_service(pref, meta):
    """Return the service int for the step API (mirrors getAvailableService() in userscript)."""
    if isinstance(pref, int):
        return pref

    # first set bit in the bitmask, priority 1 → 2 → 4
    service_bits = (meta.get("activeRevenueProfile") or {}).get("service", 0) or 0
    if service_bits & 1:
        return 1
    if service_bits & 2:
        return 2
    if service_bits & 4:
        return 4
    return 1


def _get_metadata(ticket, session):
    # retry up to 3 times on network errors; if the server says no, bail immediately
    for _ in range(3):
        try:
            j = session.get(
                f"https://auth.platorelay.com/api/session/metadata?ticket={ticket}",
                timeout=10,
            ).json()
            if j.get("success"):
                return j.get("data") or {}
            return None  # server responded but success=false — retrying won't help
        except Exception:
            time.sleep(0.3)
    return None


def _bypass_loot(loot_url):
    try:
        _TRW_KEY = "TRW_FREE-GAY-15a92945-9b04-4c75-8337-f2a6007281e9"
        url = (
            f"https://trw.lat/api/bypass"
            f"?apikey={_TRW_KEY}"
            f"&mode=stream"
            f"&url={urllib.parse.quote(loot_url, safe='')}"
        )
        # connect in 10s, then stream for up to 90s
        resp = stdlib_requests.get(url, timeout=(10, 90), stream=True)
        result_val = None
        for raw_line in resp.iter_lines():
            line = (raw_line.decode() if isinstance(raw_line, bytes) else raw_line).strip()
            if not line.startswith("data:"):
                continue
            try:
                evt = json.loads(line[5:].strip())
            except Exception:
                continue
            print(f"[bypass] {evt}")
            if evt.get("success") and evt.get("result"):
                result_val = evt["result"]
                break
            if evt.get("status") not in ("started", "processing", None):
                # terminal non-success event
                break
        if result_val:
            return result_val
        print("[bypass] no result in stream")
    except Exception as e:
        print(f"[\u2717] bypass error: {e}")
    return None

def getKey(url, verbose_cb=None, service=None, use_external_captcha=False):
    """
    Bypass a PlatoRelay checkpoint link and return the key.

    Parameters
    ----------
    url : str
        Full auth.platorelay.com URL.
    verbose_cb : callable | None
        Optional callback for progress messages, e.g. ``verbose_cb=print``.
    service : int | None
        Preferred service bitmask bit (1, 2, or 4).  When given, that value
        is sent directly.  None = auto-detect from the link's metadata bitmask,
        identical to getAvailableService() in the userscript (first set bit,
        1 → 2 → 4, default 1).

    Returns
    -------
    str
        The key on success, or a string starting with "bypass fail!" on error.
    """
    vcb = verbose_cb or (lambda msg: None)

    fp      = _random_fingerprint()
    session = _build_session(fp)
    session.headers.update({
        "Accept":           "application/json",
        "X-Client-Name":    "platoboost webclient",
        "X-Client-Version": "5.3.2",
        "Sec-Fetch-Dest":   "empty",
        "Sec-Fetch-Mode":   "cors",
        "Sec-Fetch-Site":   "same-origin",
    })
    session.headers.pop("Sec-Fetch-User", None)
    session.headers.pop("Upgrade-Insecure-Requests", None)

    try:
        ticket     = _get_param(url, "d") or _get_param(url, "ticket")
        hash_param = _get_param(url, "hash")
        screen_res = fp["resolution"]
        sw         = int(screen_res.split("x")[0])
        sh         = int(screen_res.split("x")[1])
        user_agent = fp["user_agent"]
        nav_plat   = fp["navigator_platform"]

        session.headers["Referer"] = f"https://auth.platorelay.com/a?d={ticket}"

        key = checkKey(ticket, session)
        if key:
            vcb("Key found.")
            return key

        vcb("Running bypass...")

        resolved = True

        # start solving captcha in the background before we even hit the first checkpoint
        if not use_external_captcha:
            _pre_ex = ThreadPoolExecutor(max_workers=3)
            _pre_futs = [_pre_ex.submit(_solve_captcha_once) for _ in range(3)]
            _pre_ex.shutdown(wait=False)
        else:
            _pre_futs = None
        _prefetched_cap = None

        def _harvest_pre_futs():
            # pick up a result if any of the early workers finished
            nonlocal _prefetched_cap, _pre_futs
            if not _pre_futs or _prefetched_cap:
                return
            for f in list(_pre_futs):
                if f.done():
                    tok = f.result()
                    if tok:
                        _prefetched_cap = tok
                        _pre_futs = None
                        return

        for _outer in range(20):
            _harvest_pre_futs()

            meta = _get_metadata(ticket, session)
            if meta is None:
                print("[!] metadata fetch failed")
                break

            _harvest_pre_futs()   # another ~200ms has passed since the last check

            completed   = meta.get("completed", 0)
            total       = (meta.get("activeRevenueProfile") or {}).get("checkpointCount", 0)
            et_on       = meta.get("enableEventTracker", False)
            svc         = _resolve_service(service, meta)

            vcb(f"checkpoint {completed}/{total}")

            if completed >= total:
                break

            step_url = (
                f"https://auth.platorelay.com/api/session/step"
                f"?ticket={ticket}&service={svc}"
            )
            if hash_param:
                step_url += f"&hash={hash_param}"

            mk = lambda: getMeta(ticket, screen_res, user_agent, nav_plat)
            sk = lambda: generate_stream(ticket, sw, sh) if et_on else ""

            # already have a captcha ready, skip the unnecessary first request
            if not use_external_captcha and _prefetched_cap:
                cap = _prefetched_cap
                _prefetched_cap = None
                print(f"[captcha] prefetch hit: {cap[:24]}...")
                payload = {
                    "captcha":  cap,
                    "meta":     mk(),
                    "stream":   sk(),
                    "resolved": resolved,
                }
                try:
                    resp = session.put(step_url, json=payload, timeout=15).json()
                except Exception as _e:
                    print(f"[step] PUT error: {_e}, retrying...")
                    time.sleep(0.2)
                    continue
                loot_url = (resp.get("data") or {}).get("url") if resp.get("success") else None
                if not loot_url:
                    # token got rejected, solve a fresh one
                    print(f"[step] captcha rejected, re-solving: {json.dumps(resp)[:120]}")
                    cap = solve_captcha_external() if use_external_captcha else solve_captcha()
                    if not cap:
                        print("[!] captcha failed, retrying...")
                        time.sleep(0.2)
                        continue
                    payload["captcha"] = cap
                    payload["stream"]  = sk()
                    payload["meta"]    = mk()
                    try:
                        resp = session.put(step_url, json=payload, timeout=15).json()
                    except Exception as _e:
                        print(f"[step] PUT error: {_e}, retrying...")
                        time.sleep(0.2)
                        continue
                    loot_url = (resp.get("data") or {}).get("url") if resp.get("success") else None
            else:
                # try without captcha first, some steps don't need it
                payload = {
                    "captcha":  None,
                    "meta":     mk(),
                    "stream":   sk(),
                    "resolved": resolved,
                }
                try:
                    resp = session.put(step_url, json=payload, timeout=15).json()
                except Exception as _e:
                    print(f"[step] PUT error: {_e}, retrying...")
                    time.sleep(0.2)
                    continue
                loot_url = (resp.get("data") or {}).get("url") if resp.get("success") else None

                if not loot_url:
                    msg = (resp.get("data") or {}).get("message") or resp.get("message") or ""
                    print(f"[step] {msg or json.dumps(resp)}")

                    vcb("Solving CAPTCHA...")
                    cap = solve_captcha_external() if use_external_captcha else solve_captcha()
                    if not cap:
                        print("[!] captcha failed, retrying...")
                        time.sleep(0.2)
                        continue

                    print(f"[captcha] {cap[:24]}...")
                    payload["captcha"] = cap
                    payload["stream"]  = sk()
                    payload["meta"]    = mk()
                    try:
                        resp = session.put(step_url, json=payload, timeout=15).json()
                    except Exception as _e:
                        print(f"[step] PUT error: {_e}, retrying...")
                        time.sleep(0.2)
                        continue
                    loot_url = (resp.get("data") or {}).get("url") if resp.get("success") else None

            if not loot_url:
                print(f"[step] no url — {json.dumps(resp)}")
                key = checkKey(ticket, session)
                if key:
                    return key
                time.sleep(0.2)
                continue

            vcb("Bypassing ad link...")
            print(f"[loot] {loot_url[:80]}...")

            # kick off the next captcha solve while we wait for the bypass (~6-8s)
            if not use_external_captcha:
                _cap_exe = ThreadPoolExecutor(max_workers=3)
                _cap_futs = [_cap_exe.submit(_solve_captcha_once) for _ in range(3)]
                _cap_exe.shutdown(wait=False)
            else:
                _cap_futs = None

            result = _bypass_loot(loot_url)

            # bypass takes long enough that the captcha should be done by now
            if _cap_futs and not _prefetched_cap:
                for f in list(_cap_futs):
                    if f.done():
                        tok = f.result()
                        if tok:
                            _prefetched_cap = tok
                            break
                if not _prefetched_cap:
                    try:
                        for f in as_completed(_cap_futs, timeout=3):
                            tok = f.result()
                            if tok:
                                _prefetched_cap = tok
                                break
                    except TimeoutError:
                        pass
                if _prefetched_cap:
                    print(f"[captcha] prefetch ready: {_prefetched_cap[:24]}...")

            if not result:
                print("[!] loot bypass failed, retrying...")
                time.sleep(0.2)
                continue

            print(f"[solved] {result[:80]}...")

            new_ticket = _get_param(result, "d") or _get_param(result, "ticket")
            if new_ticket:
                ticket     = new_ticket
                hash_param = _get_param(result, "hash")
                session.headers["Referer"] = f"https://auth.platorelay.com/a?d={ticket}"

            # visit both URLs at the same time to register the bypass with Plato
            def _visit(u):
                try:
                    session.get(u, timeout=3)
                except Exception:
                    pass
            _vt1 = threading.Thread(target=_visit, args=(loot_url,), daemon=True)
            _vt2 = threading.Thread(target=_visit, args=(result,), daemon=True)
            _vt1.start(); _vt2.start()
            _vt1.join(timeout=3); _vt2.join(timeout=3)

            time.sleep(0.1)

        vcb("Unlocking...")
        meta     = _get_metadata(ticket, session) or {}
        et_on    = meta.get("enableEventTracker", False)
        svc      = _resolve_service(service, meta)
        step_url = (
            f"https://auth.platorelay.com/api/session/step"
            f"?ticket={ticket}&service={svc}"
        )
        if hash_param:
            step_url += f"&hash={hash_param}"

        try:
            unlock_resp = session.put(step_url, json={
                "captcha":  None,
                "meta":     getMeta(ticket, screen_res, user_agent, nav_plat),
                "stream":   generate_stream(ticket, sw, sh) if et_on else "",
                "resolved": resolved,
            }, timeout=15).json()
            print(f"[unlock] {unlock_resp.get('success')} — {(unlock_resp.get('data') or {}).get('url', '')}")
        except Exception as _e:
            print(f"[unlock] PUT error (continuing): {_e}")

        time.sleep(0.1)

        vcb("Fetching key...")
        key = checkKey(ticket, session)
        if key:
            return key

        return "bypass fail!"

    except Exception:
        print(f"[!] {traceback.format_exc()}")
        return "bypass fail!"
    finally:
        try:
            session.close()
        except Exception:
            pass


def get_token():
    """Solve one PlatoRelay GIF CAPTCHA and return the raw token string (or None)."""
    return solve_captcha()


__all__ = ["getKey", "get_token"]


if __name__ == "__main__":
    url = input("URL: ").strip()
    result = getKey(url, verbose_cb=print)
    if result and not result.startswith("bypass fail"):
        print(f"\n[\u2713] {result}")
    else:
        print(f"\n[\u2717] {result}")
