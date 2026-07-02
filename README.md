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

> **Construction status (2026-07-02).** The field FOUNDATION is proven and
> compiles (`verification/check.sh` is green): **PPallas** (Lucas/Pratt
> primality certificate for the 255-bit Pallas modulus), **Denote** (the
> Montgomery denotation ⟪a⟫ = feVal a·R⁻¹ and the `Canon` invariant),
> **HelperSpecs** (exact ℕ specs for the `adc`/`sbb`/`mac` u64 primitives,
> proven against the transpiled code), **SubNegSpec** (`sub`/`neg`), and
> **ConstSpecs** (R, R², INV, zero, one). Every one is stated about the REAL
> Aeneas-extracted code with **no bridge axioms**.
>
> **In progress:** `add`, `mul`, `montgomery_reduce`, `square`, `invert`, and
> the aggregate `fieldImplementation` certificate. These are drafted in
> `verification/Proofs/drafts/` and the Montgomery accounting is proven
> standalone, but the full theorems currently overflow the Lean **kernel's
> proof-checking memory**: omega certificates with 2²⁵⁶/2⁵¹²-scale
> coefficients (unavoidable in 4×64 Montgomery arithmetic) are too large for
> the kernel, whereas the ed25519 5×51 field (2⁵¹-scale, ×19 folding) stays
> small. The fix — reformulating every arithmetic step via `linear_combination`
> and isolating each big-coefficient step into a context-free lemma (the
> `montgomery_rows_conclusion` accounting lemma already does this and compiles)
> — is mechanical but not yet complete. Tracked honestly here rather than
> shipped behind an axiom.

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
