#!/usr/bin/env python3
"""Render the README / web page charts as SVG (light + dark) from one data file.

    python3 -I webpage/charts/make_charts.py          # reads webpage/charts/data.json
                                                      # writes webpage/assets/*-{light,dark}.svg
                                                      # and the table views between the CHART-TABLE markers of webpage/index.html

Every number comes from data.json (null = not measured yet, drawn as "pending"); refresh the values there and re-run.
Palette: categorical slots 1-2 of the validated reference palette (blue = Light-Prover, orange = official toolchain),
checked with the palette validator in both modes. Marks: 10 px bars with a 4 px rounded data end, hairline solid grid,
values at the bar tips in text colours, one modest type scale. Each bar carries a <title> tooltip; the web page carries
a table view of every chart. A layout check (text boxes inside the card, no overlapping labels) runs on every render.

The charts are static (ANIMATE = False). With ANIMATE = True, bars grow in from the baseline once and their labels fade
in (CSS only, no script); the time-lapse chart then grows every bar at the same rate per hour. The static state of an
animated SVG is still its final frame, and prefers-reduced-motion turns the animation off.
"""
import json
import math
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "assets")
INDEX = os.path.join(HERE, "..", "index.html")
FONT = "system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
THEMES = {
    "light": dict(surface="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781", grid="#e1e0d9",
                  axis="#c3c2b7", ring="rgba(11,11,11,0.10)", ours="#2a78d6", official="#eb6834"),
    "dark": dict(surface="#1a1a19", ink="#f0efec", ink2="#c3c2b7", muted="#898781", grid="#2c2c2a",
                 axis="#383835", ring="rgba(255,255,255,0.10)", ours="#3987e5", official="#d95926"),
}
CHAR_W = 0.6   # conservative average glyph width (x font size) for the layout check
ANIMATE = False   # True: bars grow in once and labels fade in (CSS only); False: static charts (the release default)


def esc(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def fmt_dur(s):
    if s is None:
        return "pending"
    if s < 7200:   # the value as measured (up to two decimals), never rounded further
        if isinstance(s, int):
            return f"{s:,} s"
        t = f"{s:,.2f}".rstrip("0")
        return f"{t}0 s" if t.endswith(".") else f"{t} s"   # a measured 1,589.0 keeps its decimal
    return f"{s / 3600:.1f} h"


def fmt_ratio(r):
    from decimal import Decimal, ROUND_HALF_UP
    return f"{Decimal(repr(r)).quantize(Decimal('0.1'), rounding=ROUND_HALF_UP)}x"   # one decimal, half up


class Canvas:
    """Collects SVG elements and the boxes of every text, for the layout check."""

    def __init__(self, w, h, t):
        self.w, self.h, self.t, self.parts, self.texts = w, h, t, [], []
        self.defs, self.keyframes, self.animated = [], [], False

    def text(self, x, y, s, size=12, color="ink2", weight=None, anchor="start", fade=None):
        s = str(s)
        fade = fade if ANIMATE else None
        width = CHAR_W * size * len(s)
        x0 = x - width if anchor == "end" else x - width / 2 if anchor == "middle" else x
        self.texts.append((x0, y - size * 0.8, width, size, s))
        wt = f' font-weight="{weight}"' if weight else ""
        an = f' text-anchor="{anchor}"' if anchor != "start" else ""
        if fade is not None:   # fade in once, after its bar has grown
            self.animated = True
            an += f' style="animation:fd .35s ease-out {fade:.2f}s backwards"'
        self.parts.append(f'<text x="{x:.1f}" y="{y:.1f}"{an} font-family="{FONT}" font-size="{size}"{wt} '
                          f'fill="{self.t[color]}" stroke="{self.t["surface"]}" stroke-width="3" stroke-linejoin="round" '
                          f'paint-order="stroke">{esc(s)}</text>')   # a halo in the surface colour: grid lines never cross text

    def bar(self, x, y, w, h, color, tip, grow=None, left=False):
        """A bar from the baseline x; grow=(delay, duration, easing) slides it in from behind the baseline (a clip at
        the baseline keeps the rounded data end intact while the visible length grows)."""
        grow = grow if ANIMATE else None
        w = max(w, 2.5)
        r = min(4, w / 2, h / 2)
        d = f"M{x:.1f},{y:.1f} H{x + w - r:.1f} Q{x + w:.1f},{y:.1f} {x + w:.1f},{y + r:.1f} V{y + h - r:.1f} " \
            f"Q{x + w:.1f},{y + h:.1f} {x + w - r:.1f},{y + h:.1f} H{x:.1f} Z"
        if left:   # the data end is on the left (a bar below a reference line): round that end instead
            d = f"M{x + w:.1f},{y:.1f} H{x + r:.1f} Q{x:.1f},{y:.1f} {x:.1f},{y + r:.1f} V{y + h - r:.1f} " \
                f"Q{x:.1f},{y + h:.1f} {x + r:.1f},{y + h:.1f} H{x + w:.1f} Z"
        mark = f'<path d="{d}" fill="{self.t[color]}"%s><title>{esc(tip)}</title></path>'
        if grow is None:
            self.parts.append(mark % "")
        else:
            self.animated = True
            k = len(self.keyframes)
            delay, dur, ease = grow
            self.defs.append(f'<clipPath id="c{k}"><rect x="{x:.1f}" y="{y - 2:.1f}" width="{self.w - x:.1f}" '
                             f'height="{h + 4:.1f}"/></clipPath>')
            self.keyframes.append(f"@keyframes g{k}{{from{{transform:translateX(-{w + 1:.1f}px)}}}}")
            self.parts.append(f'<g clip-path="url(#c{k})">' +
                              mark % f' style="animation:g{k} {dur:.2f}s {ease} {delay:.2f}s backwards"' + "</g>")
        return x + w

    def line(self, x1, y1, x2, y2, color="grid"):
        self.parts.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{self.t[color]}" '
                          f'stroke-width="1"/>')

    def swatch(self, x, y, color):
        self.parts.append(f'<rect x="{x}" y="{y - 9}" width="10" height="10" rx="2" fill="{self.t[color]}"/>')

    def check(self, name):
        for (x, y, w, h, s) in self.texts:
            assert x >= 8 and x + w <= self.w - 8 and y >= 4 and y + h <= self.h - 4, f"{name}: text outside the card: {s!r}"
        boxes = sorted(self.texts, key=lambda b: (b[1], b[0]))
        for i, a in enumerate(boxes):
            for b in boxes[i + 1:]:
                if a[0] < b[0] + b[2] and b[0] < a[0] + a[2] and a[1] < b[1] + b[3] and b[1] < a[1] + a[3]:
                    raise AssertionError(f"{name}: overlapping labels {a[4]!r} / {b[4]!r}")

    def svg(self, title):
        head = ""
        if self.animated:   # plays once; the static state is the final frame (reduced motion: no animation at all)
            head = ("<style>" + "".join(self.keyframes) + "@keyframes fd{from{opacity:0}}"
                    "@media (prefers-reduced-motion:reduce){*{animation:none!important}}</style>\n")
        if self.defs:
            head += "<defs>" + "".join(self.defs) + "</defs>\n"
        return (f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
                f'viewBox="0 0 {self.w} {self.h}" role="img" aria-label="{esc(title)}">\n<title>{esc(title)}</title>\n'
                + head +
                f'<rect x="0.5" y="0.5" width="{self.w - 1}" height="{self.h - 1}" rx="12" fill="{self.t["surface"]}" '
                f'stroke="{self.t["ring"]}"/>\n' + "\n".join(self.parts) + "\n</svg>\n")


def lines(v):
    return v if isinstance(v, list) else [v]


BAR = 10                      # bar thickness (px)
EASE = "cubic-bezier(.2,.7,.3,1)"   # ease-out, no overshoot
GROW_S, STAGGER_S = 0.9, 0.15  # grow-in of the static charts: duration and per-row stagger


def tip_y(y):
    return y + BAR / 2 + 4    # baseline of a label centred on a bar


def header(c, title, subtitle):
    """Title and subtitle lines; returns the extra height used by subtitle lines after the first."""
    c.text(28, 36, title, 15, "ink", 500)
    for i, s in enumerate(lines(subtitle)):
        c.text(28, 58 + 16 * i, s, 12, "ink2")
    return 16 * (len(lines(subtitle)) - 1)


def footer(c, source):
    for i, s in enumerate(reversed(lines(source))):
        c.text(28, c.h - 18 - 15 * i, s, 11, "muted")


def foot_h(source):
    return 15 * (len(lines(source)) - 1)


def legend(c, x, y):
    for name, key in (("Official Lean toolchain", "official"), ("Light-Prover", "ours")):
        c.swatch(x, y, key)
        c.text(x + 16, y, name, 12, "ink2")
        x += 16 + CHAR_W * 12 * len(name) + 20


def log_axis(c, x0, x1, lo, hi, y0, y1, ticks):
    def pos(v):
        return x0 + (x1 - x0) * (math.log10(v) - math.log10(lo)) / (math.log10(hi) - math.log10(lo))
    for v, lab in ticks:
        c.line(pos(v), y0, pos(v), y1)
        c.text(pos(v), y1 + 16, lab, 11, "muted", anchor="middle")
    c.line(x0, y0, x0, y1, "axis")
    return pos


def chart_timelapse(t, d, stages):
    """Time to a verified proof, linear hours, as a time-lapse: every bar grows at the same rate per hour."""
    tot = {g["name"]: g for g in stages}
    a, b = tot["Total with (a)"], tot["Total with (b)"]
    ours = a["light_prover_s"]
    assert ours == b["light_prover_s"]
    rows = [(d["rows"][0], "ours", ours, f"{fmt_dur(ours)} ({ours / 3600:.1f} h)"),
            (d["rows"][1], "official", b["official_s"], f"{fmt_dur(b['official_s'])} ({fmt_ratio(b['official_s'] / ours)} longer)"),
            (d["rows"][2], "official", a["official_s"], f"{fmt_dur(a['official_s'])} ({fmt_ratio(a['official_s'] / ours)} longer)")]
    step = 44
    c = Canvas(800, 104 + step * len(rows) + 40, t)
    header(c, d["title"], d["subtitle"])
    x0, x1, hmax = 270, 650, 60
    sec_per_hour = d["seconds_per_hour"]   # playback rate of the time-lapse
    start = 0.4
    y = 98
    for v in range(0, hmax + 1, 10):
        x = x0 + (x1 - x0) * v / hmax
        c.line(x, y - 12, x, y + step * len(rows) - 18)
        c.text(x, y + step * len(rows) + 2, f"{v} h", 11, "muted", anchor="middle")
    c.line(x0, y - 12, x0, y + step * len(rows) - 18, "axis")
    for r, key, v, lab in rows:
        c.swatch(28, y + 8, key)
        c.text(44, y + 8, r["name"], 13, "ink")
        c.text(44, y + 24, r["detail"], 11, "muted")
        hours = v / 3600
        dur = hours * sec_per_hour
        end = c.bar(x0, y + 1, (x1 - x0) * hours / hmax, BAR, key, f"{r['name']}: {lab}", grow=(start, dur, "linear"))
        c.text(end + 8, tip_y(y + 1), lab, 12, "ink2", fade=start + dur)
        y += step
    footer(c, d["source"])
    c.check("rh-timelapse")
    return c.svg(d["title"])


def chart_rh_stages(t, d):
    dy = 16 * (len(lines(d["subtitle"])) - 1)
    rows = d["stages"]
    pair, gap = 16, 20                       # bar pitch inside a stage, space between stages
    c = Canvas(760, 150 + dy + (2 * pair + gap) * len(rows) + 22 + foot_h(d["source"]), t)
    header(c, d["title"], d["subtitle"])
    legend(c, 28, 92 + dy)
    x0, x1, lo, hi = 190, 590, 10, 360000
    ticks = [(10, "10 s"), (60, "1 min"), (600, "10 min"), (3600, "1 h"), (36000, "10 h"), (360000, "100 h")]
    y = 120 + dy
    pos = log_axis(c, x0, x1, lo, hi, y - 8, y + (2 * pair + gap) * len(rows) - 14, ticks)
    for n, g in enumerate(rows):
        c.text(28, y + pair + 3, g["name"], 12.5, "ink")
        for i, (key, sk) in enumerate((("official", "official_s"), ("ours", "light_prover_s"))):
            v = g[sk]
            by = y + i * pair
            if v is None:
                c.text(x0 + 8, tip_y(by), "pending", 12, "muted")
                continue
            lab = fmt_dur(v)
            if key == "ours" and g.get("official_s"):
                lab += f" ({fmt_ratio(g['official_s'] / v)})"
            who = "official" if key == "official" else "Light-Prover"
            delay = 0.2 + STAGGER_S * n
            end = c.bar(x0, by, pos(max(v, lo)) - x0, BAR, key, f"{g['name']}, {who}: {lab}", grow=(delay, GROW_S, EASE))
            c.text(end + 8, tip_y(by), lab, 12, "ink2", fade=delay + GROW_S * 0.8)
        y += 2 * pair + gap
    footer(c, d["source"])
    c.check("rh-stages")
    return c.svg(d["title"])


def chart_judge(t, d):
    rows = d["rows"]
    dy = 16 * (len(lines(d["subtitle"])) - 1)
    step = 36
    c = Canvas(760, 112 + dy + step * len(rows) + 40 + foot_h(d["source"]), t)
    header(c, d["title"], d["subtitle"])
    vals = [r["light_prover_s"] for r in rows if r["light_prover_s"] is not None]
    vmax = max(2000, -(-int(max(vals)) // 1000) * 1000)   # whole thousands of seconds, at least 2,000 s
    tick = 500 if vmax <= 2000 else 1000
    x0, x1 = 320, 660
    y = 100 + dy
    for v in range(0, vmax + 1, tick):
        x = x0 + (x1 - x0) * v / vmax
        c.line(x, y - 8, x, y + step * len(rows) - 12)
        c.text(x, y + step * len(rows) + 4, f"{v:,} s", 11, "muted", anchor="middle")
    c.line(x0, y - 8, x0, y + step * len(rows) - 12, "axis")
    for n, r in enumerate(rows):
        c.text(28, y + 8, r["name"], 12.5, "ink")
        c.text(28, y + 22, r["detail"], 11, "muted")
        v = r["light_prover_s"]
        by = y + 4
        if v is None:
            c.text(x0 + 8, tip_y(by), "pending", 12, "muted")
        else:
            lab = fmt_dur(v)
            delay = 0.2 + STAGGER_S * n
            end = c.bar(x0, by, (x1 - x0) * v / vmax, BAR, "ours", f"{r['name']}, {r['detail']}: {lab}",
                        grow=(delay, GROW_S, EASE))
            c.text(end + 8, tip_y(by), lab, 12, "ink2", fade=delay + GROW_S * 0.8)
        y += step
    footer(c, d["source"])
    c.check("judge")
    return c.svg(d["title"])


def chart_projects(t, d):
    rows = d["projects"]
    dy = 16 * (len(lines(d["subtitle"])) - 1)
    c = Canvas(760, 112 + dy + 30 * len(rows) + 40 + foot_h(d["source"]), t)
    header(c, d["title"], d["subtitle"])
    x0, x1, lo, hi = 250, 470, 0.5, 10
    ticks = [(0.5, "0.5x"), (1, "1x"), (2, "2x"), (5, "5x"), (10, "10x")]
    y = 92 + dy
    pos = log_axis(c, x0, x1, lo, hi, y - 6, y + 30 * len(rows) - 6, ticks)
    c.line(pos(1), y - 6, pos(1), y + 30 * len(rows) - 6, "axis")
    for p in rows:
        c.text(28, y + 13, p["name"], 12.5, "ink")
        if p["official_s"] and p["light_prover_s"]:
            r = p["official_s"] / p["light_prover_s"]
            assert lo <= r <= hi, (p["name"], r)
            lab = f"{fmt_ratio(r)} ({fmt_dur(p['official_s'])} vs {fmt_dur(p['light_prover_s'])})"
            a, b = sorted((pos(1), pos(r)))
            c.bar(a, y + 4, b - a, BAR, "ours", f"{p['name']}: {lab}", left=r < 1)
            c.text(x1 + 16, y + 13, lab, 12, "ink2")   # a label column right of the plot: no grid line crosses a label
        else:
            c.text(x0 + 8, y + 13, "pending", 12, "muted")
        y += 30
    footer(c, d["source"])
    c.check("projects")
    return c.svg(d["title"])


def html_tables(d):
    """Table views of every chart, for the web page (the accessible fallback of the SVGs)."""
    def table(caption, head, rows):
        h = "".join(f"<th>{esc(x)}</th>" for x in head)
        b = "".join("<tr>" + "".join(f"<td>{esc(x)}</td>" for x in r) + "</tr>" for r in rows)
        return f'<table><caption>{esc(caption)}</caption><thead><tr>{h}</tr></thead><tbody>{b}</tbody></table>'

    def ratio(a, b):
        return fmt_ratio(a / b) if a and b else "pending"
    out = []
    g = d["rh_stages"]
    out.append(table(g["title"], ["stage", "official tools", "Light-Prover", "ratio"],
                     [[x["name"], fmt_dur(x["official_s"]), fmt_dur(x["light_prover_s"]),
                       ratio(x["official_s"], x["light_prover_s"])] for x in g["stages"]]))
    j = d["judge"]
    out.append(table(j["title"], ["machine", "judge", "time"],
                     [[r["name"], r["detail"], fmt_dur(r["light_prover_s"])] for r in j["rows"]]))
    s = d["projects"]
    out.append(table(s["title"], ["project", "official flow", "Light-Prover", "ratio"],
                     [[p["name"], fmt_dur(p["official_s"]), fmt_dur(p["light_prover_s"]),
                       ratio(p["official_s"], p["light_prover_s"])] for p in s["projects"]]))
    return "\n".join(out)


CHARTS = [("rh-timelapse", lambda t, d: chart_timelapse(t, d["rh_timelapse"], d["rh_stages"]["stages"]), None),
          ("rh-stages", chart_rh_stages, "rh_stages"), ("judge", chart_judge, "judge"), ("projects", chart_projects, "projects")]

if __name__ == "__main__":
    data = json.load(open(os.path.join(HERE, "data.json")))
    os.makedirs(OUT, exist_ok=True)
    for name, fn, key in CHARTS:
        for mode, t in THEMES.items():
            p = os.path.join(OUT, f"{name}-{mode}.svg")
            open(p, "w").write(fn(t, data[key] if key else data))
            print("wrote", os.path.relpath(p))
    if os.path.exists(INDEX):
        html = open(INDEX).read()
        new, n = re.subn(r"(<!-- CHART-TABLES:BEGIN -->).*?(<!-- CHART-TABLES:END -->)",
                         lambda mm: mm.group(1) + "\n" + html_tables(data) + "\n" + mm.group(2), html, flags=re.S)
        if n:
            open(INDEX, "w").write(new)
            print("updated table views in", os.path.relpath(INDEX))
