import Lake
open Lake DSL

package notary where

extern_lib libfv_env_digest pkg := do
  let oFile := pkg.buildDir / "c" / "fv_env_digest.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "fv_env_digest.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let objJob ← buildO oFile srcJob weakArgs #["-O3", "-fPIC", "-Wall", "-Wextra"] "leanc"
  let libFile := pkg.staticLibDir / nameToStaticLib "fv_env_digest"
  buildStaticLib libFile #[objJob]

lean_lib FastParse where
lean_lib ParAxioms where
lean_lib PChk where
lean_lib EnvDigest where
lean_lib CCmpNotary where

lean_exe «pleanchecker-notary» where
  root := `Main

lean_exe «ccmp-notary» where
  root := `CCmpNotaryMain

lean_exe «test-digest» where
  root := `TestDigest
