# rh-minif-export: input not redistributed

`proj/` is not part of this repository: it is a 1,657-module subset ("rh-miniF") of the published Lean proof of the
Riemann hypothesis (alpo.ge), made lake-buildable (default targets restricted, empty missing library directories).
Recreate it from the published sources and place it at `tests/rh-minif-export/proj/` before running this heavy test.
Expected (original-Lean reference export of the same project): sha256 `b38f52932340a437...`.
