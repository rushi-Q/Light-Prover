# Project web page

- `index.html` - a static one-page site (no build step, no external assets). Light and dark themes follow the
  reader's system setting.
- `assets/` - the figures used by the page and by the repository README (`*-light.svg` / `*-dark.svg`).
- `charts/` - the scripts that draw them:

```bash
python3 -I webpage/charts/make_hero.py     # the framework figure
python3 -I webpage/charts/make_charts.py   # the result charts and the table views in index.html
```

Every number of the result charts lives in one file, [`charts/data.json`](charts/data.json) (seconds; `null` is drawn as
"pending"); edit it and re-run `make_charts.py`. The values are documented, with their conditions, in
[`../docs/benchmarks.md`](../docs/benchmarks.md). The charts use two categorical colors (blue for Light-Prover, orange for
the official toolchain), validated for color-vision deficiencies in both themes; every bar carries a direct label and a
hover title, so color is never the only cue, and `index.html` carries a table view of every chart. The script checks that
no label leaves its card or overlaps another.

The result charts are static. Only the framework figure (`framework-*.svg`) moves: a short dash travels along each
connector and each stage gets a faint outline in turn, in a calm 7 s loop (CSS only, no script). Its static state is the
plain figure, so renderers without CSS animation and readers who set `prefers-reduced-motion` see it unchanged.

To publish the page with GitHub Pages, serve the repository root (the page links to `../docs`).
