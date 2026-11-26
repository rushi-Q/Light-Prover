#!/bin/bash
# repro: native-stack band of the elaborator/parser. Any x86-64 host (docker). OFFICIAL lean 4.33.1 natively AND (control, same
# environment as the fast lean) inside the same ubuntu:24.04 container; FAST = the real /scratch/fastverify/tc/stage1 lean.
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fstk.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; FTC=/scratch/fastverify/tc/stage1/lib/lean
mkdir -p $W/t33/bin $W/t33/lib/lean; cp $T33/bin/lean $W/t33/bin/; cp $T33/lib/lean/*.so $W/t33/lib/lean/; cp -r $T33/lib/lean/Init $T33/lib/lean/Init.* $W/t33/lib/lean/
IMG=${FV_DOCKER_IMAGE:-$LIGHT_LEAN/repro-bin/ubuntu-24.04.tar}; docker image inspect ubuntu:24.04 >/dev/null 2>&1 || docker load -q -i "$IMG" >/dev/null
cd $W; export FL_BIND="$W"
for n in 390000 398500 401500; do
  python3 -I "$H/gen.py" $n > N$n.lean
  LEAN_PATH=$T33/lib/lean $T33/bin/lean N$n.lean > o1 2>&1; ro=$?
  docker run --rm --pull never --network none -u "$(id -u):$(id -g)" -v $W:$W -w $W -e LEAN_PATH=$W/t33/lib/lean ubuntu:24.04 $W/t33/bin/lean N$n.lean > o2 2>&1; rc=$?
  LEAN_PATH=$FTC "$H/fastlean" -Ddebug.skipKernelTC=true -Dlinter.all=false N$n.lean > o3 2>&1; rf=$?
  echo "nesting $n: official rc=$ro $(grep -o 'Stack overflow detected' o1) | official-in-container rc=$rc $(grep -o 'Stack overflow detected' o2) | fast rc=$rf $(grep -o 'Stack overflow detected' o3)"
done
