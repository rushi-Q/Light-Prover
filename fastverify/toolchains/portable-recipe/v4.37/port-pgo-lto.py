#!/usr/bin/env python3
"""port-pgo-lto.py SRC/CMakeLists.txt : port 4 build-system commits of the patched toolchain line (a3228bc450 7f813460db 3a67a908e0 79a71f74e0:
LEAN_TOOLCHAIN_CODEGEN_FLAGS, ThinLTO by default with clang+lld on Linux, clang frontend PGO LEAN_PGO_GENERATE/LEAN_PGO_USE,
-z keep-text-section-prefix) to the Lean v4.37.0-rc1 src/CMakeLists.txt. Build-system only; never embedded in leanc."""
import sys
p = sys.argv[1]; s = open(p).read()
def once(old, new):
    global s
    assert s.count(old) == 1, ("anchor not unique/absent", old[:80], s.count(old)); s = s.replace(old, new)
once('''string(APPEND LEANC_EXTRA_CC_FLAGS " -ffp-contract=off")
string(APPEND LEAN_EXTRA_CXX_FLAGS " -ffp-contract=off")
''', '''string(APPEND LEANC_EXTRA_CC_FLAGS " -ffp-contract=off")
string(APPEND LEAN_EXTRA_CXX_FLAGS " -ffp-contract=off")

# (port of team T 3a67a908e0 + 79a71f74e0 to 4.37) Profile-guided optimization of the toolchain itself (clang only; inlining /
# code layout only, no semantic change). Clang FRONTEND instrumentation (function hashes from the AST). LEAN_PGO_GENERATE=ON:
# instrumented toolchain (raw profiles to $LLVM_PROFILE_FILE); LEAN_PGO_USE=<merged .profdata> (default: <repo>/pgo/lean.profdata
# if present) optimizes the runtime, kernel and the stdlib C code. Never embedded in `leanc`: user code is unaffected.
option(LEAN_PGO_GENERATE "Build a PGO-instrumented toolchain" OFF)
if(NOT DEFINED LEAN_PGO_USE)
  set(LEAN_PGO_USE "")
  if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../pgo/lean.profdata")
    set(LEAN_PGO_USE "${CMAKE_CURRENT_SOURCE_DIR}/../pgo/lean.profdata")
  endif()
endif()
set(LEAN_PGO_FLAGS "")
set(LEAN_PGO_LINK_FLAGS "")
if(NOT (STAGE EQUAL 0) AND CMAKE_C_COMPILER_ID MATCHES "Clang" AND NOT CMAKE_SYSTEM_NAME MATCHES "Windows|Emscripten")
  if(LEAN_PGO_GENERATE)
    set(LEAN_PGO_FLAGS "-fprofile-instr-generate")
    string(APPEND CMAKE_EXE_LINKER_FLAGS " -fprofile-instr-generate")
    string(APPEND CMAKE_SHARED_LINKER_FLAGS " -fprofile-instr-generate")
  elseif(LEAN_PGO_USE)
    file(MD5 "${LEAN_PGO_USE}" LEAN_PGO_HASH)
    message(STATUS "PGO: using profile ${LEAN_PGO_USE} (md5 ${LEAN_PGO_HASH})")
    set(LEAN_PGO_FLAGS "-fprofile-instr-use=${LEAN_PGO_USE} -DLEAN_PGO_PROFILE_MD5=${LEAN_PGO_HASH} -Wno-error=profile-instr-out-of-date -Wno-profile-instr-unprofiled -Wno-profile-instr-missing")
    if(LEAN_EXTRA_LINKER_FLAGS MATCHES "-fuse-ld=lld")
      set(LEAN_PGO_LINK_FLAGS "-Wl,-z,keep-text-section-prefix")
      string(APPEND CMAKE_EXE_LINKER_FLAGS " ${LEAN_PGO_LINK_FLAGS}")
      string(APPEND CMAKE_SHARED_LINKER_FLAGS " ${LEAN_PGO_LINK_FLAGS}")
    endif()
  endif()
  string(APPEND LEAN_EXTRA_CXX_FLAGS " ${LEAN_PGO_FLAGS}")
endif()
''')
once('''string(APPEND LEANC_OPTS " ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")
''', '''string(APPEND LEANC_OPTS " ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")
# PGO flags (see above) for the links of the stdlib, likewise not embedded in `leanc`
string(APPEND LEANC_OPTS " ${LEAN_PGO_FLAGS} ${LEAN_PGO_LINK_FLAGS}")
# (port of team T a3228bc450 + 7f813460db) internal-only codegen flags for the toolchain itself (C/C++ runtime and kernel,
# Lake-compiled stdlib C, toolchain links); ThinLTO by default with clang + lld on Linux. Never embedded in `leanc`/`lake`.
set(LEAN_TOOLCHAIN_CODEGEN_FLAGS "" CACHE STRING "Additional internal compiler/linker flags for building the toolchain (not embedded in leanc)")
set(LEAN_LTO_DEFAULT OFF)
if(NOT (STAGE EQUAL 0) AND CMAKE_C_COMPILER_ID MATCHES "Clang" AND CMAKE_CXX_COMPILER_ID MATCHES "Clang"
   AND CMAKE_SYSTEM_NAME MATCHES "Linux" AND LEAN_EXTRA_LINKER_FLAGS MATCHES "-fuse-ld=lld")
  set(LEAN_LTO_DEFAULT ON)
endif()
option(LEAN_LTO "Build the toolchain itself with ThinLTO (not embedded in leanc)" ${LEAN_LTO_DEFAULT})
if(LEAN_LTO)
  string(APPEND LEAN_TOOLCHAIN_CODEGEN_FLAGS " -flto=thin")
endif()
if(LEAN_TOOLCHAIN_CODEGEN_FLAGS)
  string(APPEND CMAKE_CXX_FLAGS " ${LEAN_TOOLCHAIN_CODEGEN_FLAGS}")
  string(APPEND CMAKE_C_FLAGS " ${LEAN_TOOLCHAIN_CODEGEN_FLAGS}")
  string(APPEND LEANC_OPTS " ${LEAN_TOOLCHAIN_CODEGEN_FLAGS}")
endif()
''')
once('''toml_escape("${LEANC_EXTRA_CC_FLAGS}" LEAN_MORE_LEANC_ARGS_TOML)''',
     '''toml_escape("${LEANC_EXTRA_CC_FLAGS} ${LEAN_TOOLCHAIN_CODEGEN_FLAGS} ${LEAN_PGO_FLAGS}" LEAN_MORE_LEANC_ARGS_TOML)''')
open(p, 'w').write(s); print("ported:", p)
