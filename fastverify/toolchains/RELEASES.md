# Official Lean releases pinned for `tools/addrelease.py`

Each `leanprover--lean4---vX.json` in this directory is the whole-tree manifest (`lib/toolchain.py pin`) of the OFFICIAL
release tarball `https://github.com/leanprover/lean4/releases/download/vX/lean-X-linux.tar.zst` as unpacked by elan
(`toolchains/leanprover--lean4---vX`). Provenance of the tarballs (sha256 of the file
as served by GitHub; no code of the toolchain was run before pinning). Independent cross-check: separately made installs
of 4.34.1, 4.35.0 and 4.37.0-rc1 verify against these manifests (`toolchain.py verify`, exit 0).

| release | tarball sha256 | in the gate table (check/xversion/releases.json) | primitive targets export |
|---|---|---|---|
| 4.26.0-rc2 | 9d576f554d5134bb491d7c5acc3a024b447d2ac1b8123fcd899ef4462e162f4b | yes | ok |
| 4.26.0 | 873c252b1c6b1392e5720ad8d5a137aabbe72c9f96a930fdb5a1dd1ddc5da454 | yes | ok |
| 4.27.0 | 056e2dc8564fc064a801e69f3eb18c044b9b546bc8b0e5a2c00247f8a1cb8ce6 | yes | ok |
| 4.28.0 | ceb3a3f844f7aebf63245e2b51c28d5b0ed38942c19f93cf3febd520302160bd | yes | ok |
| 4.29.0-rc6 | bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e | yes | ok |
| 4.29.0 | 089f7e513ed3e9436d191f4986330c0b53809c86b5997f5eb7f25550c374fa48 | yes | ok |
| 4.29.1 | bf062d29556d655685fb287563c249ad6a8fde34352c18b5e32568a595c1aec1 | yes | ok |
| 4.30.0 | 4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319 | yes | ok |
| 4.31.0 | 07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f | yes | ok |
| 4.32.0-rc1 | ce6e79dd19ea03c0bc17f9d565c3bac20cd2884561e3b431e5b293c1fbb2b5b3 | yes | ok |
| 4.32.0 | fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516 | yes | ok |
| 4.33.0 | 4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c | yes | ok |
| 4.34.0-rc2 | 3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8 | yes | ok |
| 4.34.0 | caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b | yes | ok |
| 4.34.1 | 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4 | yes | ok |
| 4.35.0-rc3 | 1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997 | yes | ok |
| 4.35.0 | 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d | yes | ok |
| 4.36.0-rc1 | 26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2 | yes | ok |
| 4.36.0-rc2 | 0a0a3208617e9eab92f1041efa83ad94d405e69d172fb654a62dbfa9fbc5313b | yes | ok |
| 4.37.0-rc1 | 2e1bbb832870bb81b7131cb70b13aec2cc7ed9f22e2bdbb236b86076ae20382d | yes | ok |

Refused by `tools/addrelease.py` (not pinned): 4.15.0 (af71a256...), 4.19.0 (6fe3ce97...), 4.20.0-rc5 (e4544c44...),
4.21.0 (455c6df0...), 4.22.0 (85097a4d...), 4.24.0 (b14f5e51...), 4.25.0 (97bee7bd...): the 4.36 kernel-primitive targets
do not export from their Init (`Constant String.ofList not found`: until v4.25 the kernel expanded string literals to
`String.mk`; the 4.36 kernel expands them to `String.ofList`, so the 4.36 judge needs that constant in the challenge).

Official exporters: releases >= 4.35 bundle `bin/leanexport` (inside the pinned tree). For older releases
`tools/build-lean4export.sh` builds leanprover/lean4export at the release's tag (patch/rc without a tag: the X.Y.0 tag) with
the release's own lake, offline in bwrap; the binary's sha256 goes into config/components.json and a `.provenance` file next
to it. Builds are reproducible (e.g. lean4export v4.34.0 built twice independently with Lean
4.34.1: sha256 8c5d64ba... both; the comparator d03acab likewise afa65e57...).
