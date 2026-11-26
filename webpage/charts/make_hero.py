#!/usr/bin/env python3
"""Render the hero figure (the Light-Prover framework at a glance) as SVG, light + dark.

    python3 -I webpage/charts/make_hero.py      # writes webpage/assets/framework-{light,dark}.svg

Motion (CSS only, no script): a short dash travels along each connector, from the workflows through the untrusted
lane and the trusted judge to the verdicts, and each stage gets a faint outline in turn; a calm 7 s loop. The motion
layer is invisible in the static state (opacity 0), so renderers without CSS animation and readers who set
prefers-reduced-motion see the plain figure.
"""
import os

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "assets")
FONT = "system-ui,-apple-system,'Segoe UI',Helvetica,Arial,sans-serif"
THEMES = {
    "light": dict(bg="#fcfcfb", ink="#0b0b0b", ink2="#52514e", muted="#898781", line="#c3c2b7", hair="#e1e0d9",
                  card="#ffffff", cardring="rgba(11,11,11,0.10)", accent="#2a78d6", accent_soft="#eaf2fc",
                  accent_ring="#a9c8f0", lane="#f3f2ee", good="#006300", good_soft="#e7f3e7", warn="#8a5a00",
                  warn_soft="#fbf1dc", bad="#b3261e", bad_soft="#fbe9e7", none_soft="#efeeea"),
    "dark": dict(bg="#1a1a19", ink="#f0efec", ink2="#c3c2b7", muted="#898781", line="#4a4a46", hair="#2c2c2a",
                 card="#222221", cardring="rgba(255,255,255,0.10)", accent="#3987e5", accent_soft="#17263a",
                 accent_ring="#2f5f99", lane="#242422", good="#0ca30c", good_soft="#152a15", warn="#e0a43a",
                 warn_soft="#33290f", bad="#e66767", bad_soft="#3a1b1a", none_soft="#2a2a28"),
}


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def text(x, y, s, size=13, fill="#000", weight="400", anchor="start", spacing=None):
    ls = f' letter-spacing="{spacing}"' if spacing else ""
    return (f'<text x="{x}" y="{y}" font-family="{FONT}" font-size="{size}" font-weight="{weight}" '
            f'fill="{fill}" text-anchor="{anchor}"{ls}>{esc(s)}</text>')


def rrect(x, y, w, h, r, fill, stroke=None, sw=1, dash=None):
    st = f' stroke="{stroke}" stroke-width="{sw}"' if stroke else ""
    da = f' stroke-dasharray="{dash}"' if dash else ""
    return f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{r}" fill="{fill}"{st}{da}/>'


LOOP = 7.0   # seconds per cycle of the motion layer


def curve(x1, y1, x2, y2):
    return f"M{x1},{y1} C{(x1+x2)/2},{y1} {(x1+x2)/2},{y2} {x2-8},{y2}"


def curve_len(x1, y1, x2, y2, n=64):
    """Length of curve(x1, y1, x2, y2), sampled."""
    xm, xe = (x1 + x2) / 2, x2 - 8
    pts = []
    for i in range(n + 1):
        u = i / n
        a, b, c, e = (1 - u) ** 3, 3 * (1 - u) ** 2 * u, 3 * (1 - u) * u * u, u ** 3
        pts.append((a * x1 + b * xm + c * xm + e * xe, a * y1 + b * y1 + c * y2 + e * y2))
    return sum(((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2) ** 0.5 for p, q in zip(pts, pts[1:]))


def dash(t, d, length, start):
    """A 10 px dash that travels along the connector path d (of the given length) once per cycle, from `start` s.
    pathLength=100 normalizes the path; the dash is 10 px in those units, the gap long enough that no second dash
    ever shows."""
    dl = min(60.0, 1000.0 / length)
    return (f'<path class="fx dash" d="{d}" pathLength="100" fill="none" stroke="{t["accent"]}" stroke-width="2.25" '
            f'stroke-linecap="round" stroke-dasharray="{dl:.1f} 200" stroke-dashoffset="70" opacity="0" '
            f'style="animation-delay:{start:.2f}s"/>')


def glow(t, x, y, w, h, r, start):
    """A faint outline around a stage, shown once per cycle at `start` seconds."""
    return (f'<rect class="fx glow" x="{x}" y="{y}" width="{w}" height="{h}" rx="{r}" fill="none" stroke="{t["accent"]}" '
            f'stroke-opacity="0.45" stroke-width="1.5" opacity="0" style="animation-delay:{start:.2f}s"/>')


STYLE = (f"<style>.fx{{opacity:0;animation:{LOOP}s ease-in-out infinite both}}"
         ".dash{animation-name:dash;animation-timing-function:linear}.glow{animation-name:glow}"
         "@keyframes dash{0%{stroke-dashoffset:70;opacity:0}3%{opacity:.85}11%{opacity:.85}14%{stroke-dashoffset:-100;opacity:0}"
         "100%{stroke-dashoffset:-100;opacity:0}}"
         "@keyframes glow{0%{opacity:0}5%{opacity:1}13%{opacity:1}19%{opacity:0}100%{opacity:0}}"
         "@media (prefers-reduced-motion:reduce){.fx{animation:none!important;opacity:0!important}}</style>")


def arrow(t, x1, y1, x2, y2, color=None):
    c = color or t["line"]
    return (f'<path d="{curve(x1, y1, x2, y2)}" fill="none" stroke="{c}" '
            f'stroke-width="1.5"/><path d="M{x2-9},{y2-4.5} L{x2},{y2} L{x2-9},{y2+4.5} Z" fill="{c}"/>')


def hero(t):
    W, H = 1200, 662
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" role="img" '
         f'aria-label="Light-Prover framework: real workflows feed an untrusted fast build and export; a small trusted '
         f'judge produces the verdict">',
         STYLE,
         rrect(0.5, 0.5, W - 1, H - 1, 16, t["bg"], t["cardring"])]
    # header
    o.append(text(40, 54, "LIGHT-PROVER", 12, t["accent"], "700", spacing="2"))
    o.append(text(40, 84, "Sound verification of Lean 4 proofs against a pinned challenge", 22, t["ink"], "600"))
    o.append(text(40, 110, "Most of the speed sits outside a small, pinned judge: a bug in the fast path can cost a verdict, "
                  "not turn an invalid proof into ACCEPTED.", 13.5, t["ink2"]))

    # column 1: real workflows
    cx, cy, cw = 40, 150, 240
    o.append(text(cx, cy, "REAL WORKFLOWS", 11, t["muted"], "700", spacing="1.5"))
    flows = [("Proof engineering", "a verdict on every edit and commit"),
             ("AI provers & RL", "a sound verdict per attempt"),
             ("CI on proof repositories", "pull-request gates (experimental)"),
             ("Final sign-off", "large proofs such as the RH proof")]
    fy = cy + 16
    centers = []
    for name, sub in flows:
        o.append(rrect(cx, fy, cw, 64, 12, t["card"], t["cardring"]))
        o.append(text(cx + 18, fy + 28, name, 14.5, t["ink"], "600"))
        o.append(text(cx + 18, fy + 48, sub, 12, t["ink2"]))
        centers.append(fy + 32)
        fy += 78

    # column 2: engine
    ex, ey, ew, eh = 320, 150, 600, 400
    o.append(text(ex, ey, "THE ENGINE", 11, t["muted"], "700", spacing="1.5"))
    # interfaces bar
    iy = ey + 16
    o.append(rrect(ex, iy, ew, 46, 12, t["card"], t["cardring"]))
    ifs = ["CLI", "per-edit daemon", "attempt service", "HTTP · MCP", "CI action"]
    widths = [11 + 7.0 * len(name) for name in ifs]
    gap = (ew - 36 - sum(widths)) / (len(ifs) - 1)   # chips spread evenly across the bar
    ix = ex + 18
    for name, wv in zip(ifs, widths):
        o.append(rrect(round(ix, 1), iy + 11, wv, 24, 12, t["lane"]))
        o.append(text(round(ix + wv / 2, 1), iy + 27, name, 11.5, t["ink2"], "500", "middle"))
        ix += wv + gap
    # untrusted lane
    uy = iy + 66
    o.append(rrect(ex, uy, ew, 104, 12, t["lane"], t["line"], 1, "4 4"))
    o.append(text(ex + 18, uy + 22, "UNTRUSTED  ·  FAST", 10.5, t["muted"], "700", spacing="1.2"))
    stages = [("Build", "PGO toolchain, zygote fork,", "Lake-planned scheduler"),
              ("Export", "native exporter,", "byte-identical output"),
              ("Reuse", "incremental (experimental),", "auto-tuned per host")]
    sx, sw = ex + 18, 182
    for i, (name, a, b) in enumerate(stages):
        o.append(rrect(sx, uy + 32, sw, 60, 10, t["card"], t["cardring"]))
        o.append(text(sx + 14, uy + 54, name, 13.5, t["ink"], "600"))
        o.append(text(sx + 14, uy + 71, a, 10.5, t["ink2"]))
        o.append(text(sx + 14, uy + 85, b, 10.5, t["ink2"]))
        sx += sw + 9
    # trusted core
    ty = uy + 124
    o.append(rrect(ex, ty, ew, 150, 14, t["accent_soft"], t["accent_ring"], 1.5))
    o.append(text(ex + 18, ty + 24, "TRUSTED JUDGE  ·  SMALL AND FIXED", 10.5, t["accent"], "700", spacing="1.2"))
    core = [("Pinned challenge", "official export,", "sha256-pinned"),
            ("Official judge", "statements and", "axioms compared"),
            ("Official kernel", "every declaration,", "parallel replay"),
            ("Second kernel", "independent,", "mandatory veto")]
    kx, kw = ex + 18, 134
    for name, a, b in core:
        o.append(rrect(kx, ty + 38, kw, 92, 10, t["card"], t["accent_ring"]))
        o.append(text(kx + 12, ty + 64, name, 12, t["ink"], "600"))
        o.append(text(kx + 12, ty + 86, a, 11, t["ink2"]))
        o.append(text(kx + 12, ty + 102, b, 11, t["ink2"]))
        kx += kw + 9
    # flow arrows workflows -> engine
    for c in centers:
        o.append(arrow(t, cx + cw, c, ex, iy + 23))
    # down arrow interfaces -> lane
    o.append(f'<path d="M{ex+ew/2},{iy+46} V{uy-1}" stroke="{t["line"]}" stroke-width="1.5"/>'
             f'<path d="M{ex+ew/2-4.5},{uy-9} L{ex+ew/2},{uy} L{ex+ew/2+4.5},{uy-9} Z" fill="{t["line"]}"/>')
    # down arrow lane -> core
    o.append(f'<path d="M{ex+ew/2},{uy+104} V{ty-1}" stroke="{t["line"]}" stroke-width="1.5"/>'
             f'<path d="M{ex+ew/2-4.5},{ty-9} L{ex+ew/2},{ty} L{ex+ew/2+4.5},{ty-9} Z" fill="{t["line"]}"/>')
    o.append(text(ex + ew / 2 + 10, uy + 118, "export", 10.5, t["muted"]))

    # column 3: verdicts
    vx, vy, vw = 960, 150, 200
    o.append(text(vx, vy, "VERDICTS", 11, t["muted"], "700", spacing="1.5"))
    verdicts = [("ACCEPTED", "statements derivable from", "the permitted axioms", t["good"], t["good_soft"]),
                ("CONDITIONAL", "accepted modulo the listed", "open sorry lemmas", t["warn"], t["warn_soft"]),
                ("REJECTED", "with the reason", "(statement, axiom, kernel)", t["bad"], t["bad_soft"]),
                ("NO VERDICT", "declined or failed safely;", "never counted as accepted", t["ink2"], t["none_soft"])]
    yy = vy + 16
    for name, a, b, col, soft in verdicts:
        o.append(rrect(vx, yy, vw, 70, 12, soft))
        o.append(f'<rect x="{vx}" y="{yy}" width="4" height="70" rx="2" fill="{col}"/>')
        o.append(text(vx + 18, yy + 26, name, 13, col, "700", spacing="0.6"))
        o.append(text(vx + 18, yy + 45, a, 11.5, t["ink2"]))
        o.append(text(vx + 18, yy + 60, b, 11.5, t["ink2"]))
        yy += 82
    o.append(arrow(t, ex + ew, ty + 75, vx, vy + 16 + 82 + 76, t["accent"]))

    # bottom band: runs on
    by = 562
    o.append(f'<line x1="40" y1="{by-14}" x2="{W-40}" y2="{by-14}" stroke="{t["hair"]}"/>')
    o.append(text(40, by + 10, "RUNS ON", 11, t["muted"], "700", spacing="1.5"))
    tiers = ["Linux x86-64", "laptop-class 16 GB · small projects", "64-256 GB · judging large exports",
             "384-thread server", "Lean 4.26 - 4.37.0-rc1"]
    tx = 130
    for name in tiers:
        wv = 22 + 7.1 * len(name)
        o.append(rrect(tx, by - 6, wv, 26, 13, t["card"], t["cardring"]))
        o.append(text(tx + wv / 2, by + 11, name, 11.5, t["ink2"], "500", "middle"))
        tx += wv + 10
    o.append(text(40, by + 48, "RH proof, 175,187 modules, from sources on one 384-thread server: about 30 minutes. The official "
                  "toolchain with default settings took 55.7 h on the same server while it was shared;", 12, t["ink2"]))
    o.append(text(40, by + 66, "with one allocator setting the official kernel replay alone took 13 h 13 min.", 12, t["ink2"]))

    # motion layer: invisible unless CSS animation runs (timings in seconds within one LOOP)
    o.append(glow(t, cx - 4, cy + 12, cw + 8, 4 * 78 - 14 + 8, 15, 0.0))
    for i, c in enumerate(centers):
        o.append(dash(t, curve(cx + cw, c, ex, iy + 23), curve_len(cx + cw, c, ex, iy + 23), 0.6 + 0.08 * i))
    o.append(glow(t, ex - 4, iy - 4, ew + 8, 54, 15, 1.4))
    o.append(dash(t, f"M{ex+ew/2},{iy+46} V{uy-1}", uy - 1 - iy - 46, 2.0))
    o.append(glow(t, ex - 4, uy - 4, ew + 8, 112, 15, 2.6))
    o.append(dash(t, f"M{ex+ew/2},{uy+104} V{ty-1}", ty - 1 - uy - 104, 3.4))
    o.append(glow(t, ex - 4, ty - 4, ew + 8, 158, 17, 3.9))
    o.append(dash(t, curve(ex + ew, ty + 75, vx, vy + 16 + 82 + 76), curve_len(ex + ew, ty + 75, vx, vy + 16 + 82 + 76), 4.7))
    o.append(glow(t, vx - 4, vy + 12, vw + 8, 4 * 82 - 12 + 8, 15, 5.3))
    o.append("</svg>")
    return "\n".join(o)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    for mode, t in THEMES.items():
        p = os.path.join(OUT, f"framework-{mode}.svg")
        open(p, "w").write(hero(t))
        print("wrote", os.path.relpath(p))
