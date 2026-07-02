# pasta-pallas-verified

Formal verification of Pallas (Pasta curve cycle, Zcash Halo 2) arithmetic in
**zcash/pasta_curves**, built as a coherent proof pyramid in Lean 4 via the
Charon/Aeneas transpilation pipeline:

```
        ┌────────────────────────────────────┐
        │  Scalar multiplication             │   [n]P correct over the group
        ├────────────────────────────────────┤
        │  Group law (short Weierstrass)     │   point ops = curve group law
        ├────────────────────────────────────┤
        │  Field 𝔽_p (Montgomery form)       │   4×64-limb Fp ops correct mod p
        └────────────────────────────────────┘
   p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
```

Every theorem is stated about the **actual Aeneas-transpiled Rust code** from
`src/fields/fp.rs` / `src/curves.rs`. There are **no bridge axioms**: the
correctness of add/sub/neg/mul/square/montgomery_reduce/invert is *proven*,
not assumed. (A previous attempt at this target axiomatized exactly those
statements; this repository exists to do it properly.)

## Layer status

> **Construction note (2026-07-02):** the field layer is mid-build. PROVEN and
> compiled: PPallas (primality), Denote (Montgomery denotation), HelperSpecs
> (adc/sbb/mac), SubNegSpec (sub/neg). DRAFTED, awaiting compilation:
> AddSpec, ConstSpecs, ReduceSpec (Montgomery reduction), MulSpec. Not yet
> written: SquareSpec, InvertSpec, FieldMain (the certificate), check.sh.
> This note is removed when `verification/check.sh` goes green end-to-end.

| Layer | Certificate | Status | Axioms of certificate |
|-------|-------------|--------|-----------------------|
| Field 𝔽_p (Montgomery) | `fieldImplementation` | ⏳ in progress | — |
| Group law (Pallas)      | `curveImplementation` | ⏳ in progress | — |
| Scalar multiplication   | `scalarMulCorrect`    | ⏳ in progress | — |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

## Source

- **Upstream**: [zcash/pasta_curves](https://github.com/zcash/pasta_curves), commit `fe08536`
- **Pinned/patched source**: [saymrwulf/pasta_curves-source](https://github.com/saymrwulf/pasta_curves-source), commit `7f32788`
- Representation: 4×64-bit limbs, Montgomery form (a·R mod p, R = 2²⁵⁶)

## Toolchain (pinned)

| Component | Version |
|-----------|---------|
| Aeneas    | `bf13c42e` |
| Charon    | `9dd7f23c` |
| Lean      | `v4.30.0-rc2` |
| OCaml     | `5.3.0` |

## Reproducing

```bash
source ~/aeneas-toolchain/env.sh
cd verification
./extract.sh    # Rust → LLBC → Lean (regenerates gen/)
./check.sh      # compiles EVERY shipped file + axiom-audits EVERY certificate
```

## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md).
