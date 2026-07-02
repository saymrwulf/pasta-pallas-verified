#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the Rust sources.
#
# SCOPE: Pallas base field 𝔽_p (src/fields/fp.rs) + the u64 helper primitives
#        (src/arithmetic/fields.rs: adc/sbb/mac — translated TRANSPARENTLY,
#        they are plain u128 arithmetic; no hand models).
#
#   Rust --charon--> PallasFp.llbc --aeneas--> gen/PallasFp/*.lean
#
# Opaque items (documented in TRUSTED-BASE.md; all outside certificate cones):
#   * trait impls needing RNG / serde / GPU / iterator machinery
#   * sqrt (table-driven; out of scope for the field certificate)
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/pasta_curves-source

echo "[1/2] charon: Rust -> LLBC (fields::fp + arithmetic helpers)"
cd "$CRATE"
charon cargo --preset=aeneas \
  --start-from crate::fields::fp \
  --opaque 'crate::fields::fp::_::fmt' \
  --opaque 'crate::fields::fp::_::pow_by_t_minus1_over2' \
  --opaque 'crate::fields::fp::_::get_lower_32' \
  --opaque 'crate::fields::fp::_::ZETA' \
  --opaque 'crate::fields::fp::_::from_uniform_bytes' \
  --opaque 'crate::fields::fp::_::sqrt' \
  --opaque 'crate::fields::fp::_::sqrt_ratio' \
  --opaque 'crate::fields::fp::_::random' \
  --opaque 'crate::fields::fp::_::sum' \
  --opaque 'crate::fields::fp::_::product' \
  --opaque 'crate::fields::fp::_::cmp' \
  --opaque 'crate::fields::fp::_::partial_cmp' \
  --dest-file "$HERE/PallasFp.llbc" \
  -- --no-default-features

echo "[2/2] aeneas: LLBC -> Lean (split files, PallasFp.* modules)"
cd "$HERE"
aeneas -backend lean -split-files -subdir PallasFp -dest gen PallasFp.llbc

echo "Done. Now run ./check.sh to type-check the regenerated model."
