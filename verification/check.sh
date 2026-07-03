#!/usr/bin/env bash
# THE button for the pasta field FOUNDATION (what is proven & compiles today).
# Layers add/mul/reduce/square/invert/FieldMain are drafted but withheld from
# this manifest pending a kernel-certificate reformulation (see README + the
# standalone-proven accounting lemma in Proofs/_Accounting.lean). Nothing in
# this manifest depends on them; every file here compiles axiom-clean.
set -uo pipefail
source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"
GEN=(PallasFp/TypesExternal PallasFp/Types PallasFp/FunsExternal PallasFp/Funs)
PROOFS=(PPallas Denote HelperSpecs SubNegSpec ConstSpecs)

echo "=== Phase 1: stub/axiom-smuggling audit ==="
if grep -rn 'by trivial' "$HERE"/Proofs/*Spec*.lean 2>/dev/null; then echo STUB; exit 1; fi
if grep -rn ' : True :=' "$HERE"/Proofs/*.lean 2>/dev/null; then echo STUB; exit 1; fi
if grep -rnE '^(private |protected |noncomputable )*axiom ' "$HERE"/Proofs/*.lean 2>/dev/null; then
  echo "AXIOM under Proofs/ — forbidden"; exit 1; fi
echo "  clean"

echo "=== Phase 2: compile (guarded) ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  for m in ${GEN[*]}; do
    echo \"  · gen \$m\"
    LEAN_TIMEOUT=300 LEAN_MEM_MB=6144 '$HERE/lean-guard' \"\$m.lean\" || exit 1
  done
  cd '$HERE'
  for m in ${PROOFS[*]}; do
    echo \"  · proof \$m\"
    LEAN_TIMEOUT=400 LEAN_MEM_MB=8192 '$HERE/lean-guard' \"Proofs/\$m.lean\" || exit 1
  done
" || { echo FAIL; exit 1; }
echo "=== Phase 3: axiom audit (kernel-level) ==="
cd "$AENEAS_LEAN"
lake env bash -c "
  set -uo pipefail
  export LEAN_PATH=\"\$LEAN_PATH:$HERE/gen:$HERE\"
  cd '$HERE'
  AUD=\$(mktemp '$HERE/.audit-pasta-XXXX.lean')
  { echo 'import Proofs.Denote'
    echo 'import Proofs.SubNegSpec'
    echo 'import Proofs.ConstSpecs'
    echo '#print axioms PastaProofs.P_prime'
    echo '#print axioms PastaProofs.sub_spec'
    echo '#print axioms PastaProofs.INV_spec'
  } > \"\$AUD\"
  OUT=\$(LEAN_TIMEOUT=180 LEAN_MEM_MB=4096 '$HERE/lean-guard' \"\$AUD\" 2>&1)
  echo \"\$OUT\"
  rm -f \"\$AUD\" \"\${AUD%.lean}.olean\"
  N=\$(echo \"\$OUT\" | grep -cF \"depends on axioms: [propext, Classical.choice, Quot.sound]\" || true)
  [ \"\$N\" -eq 3 ] || { echo \"AXIOM AUDIT FAILED: \$N/3 clean\"; exit 1; }
" || { echo FAIL; exit 1; }
echo "  3/3 certificates axiom-clean"

echo ""
echo "PASTA FOUNDATION: ALL PROOFS PASS (primality, denotation, adc/sbb/mac, sub/neg, constants)."
