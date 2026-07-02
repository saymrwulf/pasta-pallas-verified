/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/AddSpec.lean — addition of the transpiled Fp.

   RUST ANALOG (src/fields/fp.rs:392-403): 4-limb adc chain computing the raw
   sum d = a + b (the final carry is PROVABLY zero: a, b < p < 2²⁵⁵ so
   a + b < 2²⁵⁶), followed by `(&Fp(d)).sub(&MODULUS)` — the same conditional
   reduction proven general in Proofs/SubNegSpec.lean (d < 2P shape).

   SPEC (exact ℕ, additive):
     Canon a → Canon b →
     add a b = ok r  with  Canon r ∧ (r = a + b  ∨  r + P = a + b).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.SubNegSpec
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PastaProofs

open Aeneas.Std.WP

macro "dis" : tactic =>
  `(tactic| (subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac))

/-- `Fp::add`: total, canonical, exact value (see file header). -/
theorem add_spec (a b : Fe) (ha : Canon a) (hb : Canon b) :
    fields.fp.Fp.add a b
      ⦃ r => Canon r ∧
             (feVal r = feVal a + feVal b ∨
              feVal r + P = feVal a + feVal b) ⦄ := by
  obtain ⟨a0, a1, a2, a3, hla⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, hlb⟩ := Fe.exists_limbs b
  unfold Canon at ha hb
  rw [feVal_eq a a0 a1 a2 a3 hla] at ha
  rw [feVal_eq b b0 b1 b2 b3 hlb] at hb
  unfold fields.fp.Fp.add
  let* ⟨ i, hi ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i1, hi1 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d0, carry0, hadc0 ⟩ ← adc_spec by dis
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i3, hi3 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d1, carry1, hadc1 ⟩ ← adc_spec by dis
  let* ⟨ i4, hi4 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i5, hi5 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d2, carry2, hadc2 ⟩ ← adc_spec by dis
  let* ⟨ i6, hi6 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i7, hi7 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d3, carry3, hadc3 ⟩ ← adc_spec by dis
  -- identify reads
  have hv_i : i.val = a0.val := by simp [hi, hla]
  have hv_i1 : i1.val = b0.val := by simp [hi1, hlb]
  have hv_i2 : i2.val = a1.val := by simp [hi2, hla]
  have hv_i3 : i3.val = b1.val := by simp [hi3, hlb]
  have hv_i4 : i4.val = a2.val := by simp [hi4, hla]
  have hv_i5 : i5.val = b2.val := by simp [hi5, hlb]
  have hv_i6 : i6.val = a3.val := by simp [hi6, hla]
  have hv_i7 : i7.val = b3.val := by simp [hi7, hlb]
  have hb_d0 : d0.val < 2^64 := by scalar_tac
  have hb_d1 : d1.val < 2^64 := by scalar_tac
  have hb_d2 : d2.val < 2^64 := by scalar_tac
  have hb_d3 : d3.val < 2^64 := by scalar_tac
  -- the raw sum: Σd + 2²⁵⁶·carry3 = a + b < 2P < 2²⁵⁶, hence carry3 = 0
  have hsum : limbsVal d0 d1 d2 d3 + 2^256 * carry3.val =
      limbsVal a0 a1 a2 a3 + limbsVal b0 b1 b2 b3 := by
    unfold limbsVal at *
    omega
  -- the conditional reduction: sub (Σd) MODULUS with Σd < 2P
  have hMle : feVal fields.fp.MODULUS ≤ P := le_of_eq feVal_MODULUS
  have hdlt : feVal (Array.make 4#usize [d0, d1, d2, d3] (by simp)) <
      feVal fields.fp.MODULUS + P := by
    rw [feVal_MODULUS, feVal_make]
    unfold limbsVal P at *
    omega
  -- MEMORY DISCIPLINE (post 2026-07-02 OOM): sub_spec's two arithmetic
  -- preconditions are discharged by EXACT matches against the facts proven
  -- above — never by the blanket `dis` (simp [*] + scalar_tac saturates in
  -- this ~60-hypothesis context and allocates without bound).
  let* ⟨ r, hr_canon, hr_val ⟩ ← sub_spec by
    (first | exact hMle | exact hdlt)
  -- conclude
  rw [feVal_eq a a0 a1 a2 a3 hla, feVal_eq b b0 b1 b2 b3 hlb]
  refine ⟨hr_canon, ?_⟩
  rw [feVal_MODULUS, feVal_make] at hr_val
  unfold Canon limbsVal P at *
  omega

end PastaProofs
