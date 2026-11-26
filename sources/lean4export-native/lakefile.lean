import Lake
open System Lake DSL

package lean4export where
  testDriver := "Test"

lean_lib Export

lean_lib Test

/-! Native exporter core (C++, compiled with the system C++ compiler, linked into the executable). -/

input_file fast_export.cpp where
  path := "native" / "fast_export.cpp"
  text := true

input_file nostdcxx.h where
  path := "native" / "nostdcxx.h"
  text := true

input_file osink.h where
  path := "native" / "osink.h"
  text := true

-- The official toolchain links with LLVM libc++ (no GNU libstdc++): native/nostdcxx.h + -fno-exceptions -fno-rtti
-- keep the object free of libstdc++ runtime symbols (see there).
target fast_export.o pkg : FilePath := do
  let srcJob ← fast_export.cpp.fetch
  let hdrJob ← nostdcxx.h.fetch
  let sinkJob ← osink.h.fetch
  let oFile := pkg.buildDir / "native" / "fast_export.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let extraTrace : JobM BuildTrace := do
    let hdr ← hdrJob.await
    let sink ← sinkJob.await
    return ((← getLeanTrace).mix (← computeTrace (TextFilePath.mk hdr))).mix (← computeTrace (TextFilePath.mk sink))
  -- F04: the githash of the Lean running this lakefile (= the toolchain that builds and links the exporter) is compiled
  -- in; the native core rejects (declines) .olean files with any other githash, as the official reader does.
  let ghArg := "-DF04_EXPECTED_GITHASH=\"" ++ Lean.githash ++ "\""
  buildO oFile srcJob weakArgs #["-O2", "-std=c++17", "-fPIC", "-pthread", "-fno-exceptions", "-fno-rtti", ghArg] "c++" extraTrace

@[default_target]
lean_exe lean4export where
  root := `Main
  supportInterpreter := true
  moreLinkObjs := #[fast_export.o]
