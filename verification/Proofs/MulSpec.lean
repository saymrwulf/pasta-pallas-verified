/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/MulSpec.lean — multiplication of the transpiled Fp.

   RUST ANALOG (src/fields/fp.rs:367-370 / 423-447):
   `mul = montgomery_reduce ∘ mul_unreduced`, where mul_unreduced is the
   schoolbook 4×4 product: row i (multiplier aᵢ) runs a 4-step mac chain over
   b's limbs, accumulating into the running 8-limb result.

   PROOF ARCHITECTURE
   1. `mul_unreduced_spec` — the EXACT 512-bit identity
          Σ uₖ·2^(64k) = feVal a · feVal b
      The 16 mac equations are summed with weights 2^(64(i+j)) — the
      cross-products aᵢ·bⱼ are NONLINEAR atoms, so this is `linear_combination`
      over ℤ (after zify), NOT omega. Intermediate accumulators and carries
      telescope away by construction.
   2. `mul_spec` — compose with montgomery_reduce_spec (t = a·b < P² < 2²⁵⁶·P)
      to get   Canon r ∧ (feVal r · 2²⁵⁶) % P = (feVal a · feVal b) % P,
      i.e. ⟪r⟫ = ⟪a⟫·⟪b⟫ after the denotation absorbs both R factors
      (packaged in FieldMain).

   MEMORY DISCIPLINE: cheap-first `dix` discharge; the linear_combination is
   one closed-form certificate (no search).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ReduceSpec
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PastaProofs

open Aeneas.Std.WP

macro "dix" : tactic =>
  `(tactic| (first | scalar_tac | (subst_vars; simp [Array.set_val_eq, *]; scalar_tac)))

/-- 8-limb value (the unreduced product). -/
def limbsVal8 (u0 u1 u2 u3 u4 u5 u6 u7 : U64) : ℕ :=
  u0.val + 2^64 * u1.val + 2^128 * u2.val + 2^192 * u3.val +
  2^256 * u4.val + 2^320 * u5.val + 2^384 * u6.val + 2^448 * u7.val

/-- `mul_unreduced` computes the exact 512-bit product. -/
theorem mul_unreduced_spec (a b : Fe) (a0 a1 a2 a3 b0 b1 b2 b3 : U64)
    (hla : (↑a : List U64) = [a0, a1, a2, a3])
    (hlb : (↑b : List U64) = [b0, b1, b2, b3]) :
    fields.fp.Fp.mul_unreduced a b
      ⦃ u => ∃ u0 u1 u2 u3 u4 u5 u6 u7 : U64,
             (↑u : List U64) = [u0, u1, u2, u3, u4, u5, u6, u7] ∧
             limbsVal8 u0 u1 u2 u3 u4 u5 u6 u7 =
               limbsVal a0 a1 a2 a3 * limbsVal b0 b1 b2 b3 ⦄ := by
  unfold fields.fp.Fp.mul_unreduced
  let* ⟨ i, hi ⟩ ← Array.index_usize_spec by dix
  let* ⟨ i1, hi1 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r0, carry, hm00 ⟩ ← mac_spec by dix
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r1, carry1, hm01 ⟩ ← mac_spec by dix
  let* ⟨ i3, hi3 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r2, carry2, hm02 ⟩ ← mac_spec by dix
  let* ⟨ i4, hi4 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r3, r4, hm03 ⟩ ← mac_spec by dix
  let* ⟨ i5, hi5 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r11, carry3, hm10 ⟩ ← mac_spec by dix
  let* ⟨ r21, carry4, hm11 ⟩ ← mac_spec by dix
  let* ⟨ r31, carry5, hm12 ⟩ ← mac_spec by dix
  let* ⟨ r41, r5, hm13 ⟩ ← mac_spec by dix
  let* ⟨ i6, hi6 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r22, carry6, hm20 ⟩ ← mac_spec by dix
  let* ⟨ r32, carry7, hm21 ⟩ ← mac_spec by dix
  let* ⟨ r42, carry8, hm22 ⟩ ← mac_spec by dix
  let* ⟨ r51, r6, hm23 ⟩ ← mac_spec by dix
  let* ⟨ i7, hi7 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r33, carry9, hm30 ⟩ ← mac_spec by dix
  let* ⟨ r43, carry10, hm31 ⟩ ← mac_spec by dix
  let* ⟨ r52, carry11, hm32 ⟩ ← mac_spec by dix
  let* ⟨ r61, r7, hm33 ⟩ ← mac_spec by dix
  -- identify the limb reads
  have hv_i : i.val = a0.val := by simp [hi, hla]
  have hv_i1 : i1.val = b0.val := by simp [hi1, hlb]
  have hv_i2 : i2.val = b1.val := by simp [hi2, hlb]
  have hv_i3 : i3.val = b2.val := by simp [hi3, hlb]
  have hv_i4 : i4.val = b3.val := by simp [hi4, hlb]
  have hv_i5 : i5.val = a1.val := by simp [hi5, hla]
  have hv_i6 : i6.val = a2.val := by simp [hi6, hla]
  have hv_i7 : i7.val = a3.val := by simp [hi7, hla]
  rw [hv_i, hv_i1, hv_i2, hv_i3, hv_i4] at *
  rw [hv_i5] at hm10 hm11 hm12 hm13
  rw [hv_i6] at hm20 hm21 hm22 hm23
  rw [hv_i7] at hm30 hm31 hm32 hm33
  refine ⟨r0, r11, r22, r33, r43, r52, r61, r7, rfl, ?_⟩
  -- the exact 512-bit identity: weighted sum of the 16 mac equations.
  unfold limbsVal8 limbsVal
  zify at hm00 hm01 hm02 hm03 hm10 hm11 hm12 hm13
          hm20 hm21 hm22 hm23 hm30 hm31 hm32 hm33 ⊢
  linear_combination
    hm00 + 2^64 * hm01 + 2^128 * hm02 + 2^192 * hm03 +
    2^64 * hm10 + 2^128 * hm11 + 2^192 * hm12 + 2^256 * hm13 +
    2^128 * hm20 + 2^192 * hm21 + 2^256 * hm22 + 2^320 * hm23 +
    2^192 * hm30 + 2^256 * hm31 + 2^320 * hm32 + 2^384 * hm33

/-- `Fp::mul`: total, canonical, r·R ≡ a·b (mod p). -/
theorem mul_spec (a b : Fe) (ha : Canon a) (hb : Canon b) :
    fields.fp.Fp.mul a b
      ⦃ r => Canon r ∧
             (feVal r * 2^256) % P = (feVal a * feVal b) % P ⦄ := by
  obtain ⟨a0, a1, a2, a3, hla⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, hlb⟩ := Fe.exists_limbs b
  unfold fields.fp.Fp.mul
  let* ⟨ u, hu ⟩ ← mul_unreduced_spec by
    (first | exact hla | exact hlb)
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hlu, huval⟩ := hu
  let* ⟨ j0, hj0 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j1, hj1 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j2, hj2 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j3, hj3 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j4, hj4 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j5, hj5 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j6, hj6 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ j7, hj7 ⟩ ← Array.index_usize_spec by dix
  have he0 : j0 = u0 := by simp [hj0, hlu]
  have he1 : j1 = u1 := by simp [hj1, hlu]
  have he2 : j2 = u2 := by simp [hj2, hlu]
  have he3 : j3 = u3 := by simp [hj3, hlu]
  have he4 : j4 = u4 := by simp [hj4, hlu]
  have he5 : j5 = u5 := by simp [hj5, hlu]
  have he6 : j6 = u6 := by simp [hj6, hlu]
  have he7 : j7 = u7 := by simp [hj7, hlu]
  subst he0 he1 he2 he3 he4 he5 he6 he7
  -- t = a·b < P·P ≤ 2²⁵⁶·P: montgomery_reduce's precondition
  unfold Canon at ha hb
  rw [feVal_eq a a0 a1 a2 a3 hla] at ha
  rw [feVal_eq b b0 b1 b2 b3 hlb] at hb
  have hbound : limbsVal u0 u1 u2 u3 + 2^256 * limbsVal u4 u5 u6 u7 <
      2^256 * P := by
    have h1 : limbsVal a0 a1 a2 a3 * limbsVal b0 b1 b2 b3 < P * P :=
      Nat.mul_lt_mul'' ha hb
    have h2 : P * P ≤ 2^256 * P := by
      apply Nat.mul_le_mul_right
      unfold P
      norm_num
    have h3 : limbsVal u0 u1 u2 u3 + 2^256 * limbsVal u4 u5 u6 u7 =
        limbsVal8 u0 u1 u2 u3 u4 u5 u6 u7 := by
      unfold limbsVal limbsVal8
      ring
    rw [h3, huval]
    omega
  let* ⟨ r, hr_canon, hr_val ⟩ ← montgomery_reduce_spec by
    exact hbound
  refine ⟨hr_canon, ?_⟩
  rw [feVal_eq a a0 a1 a2 a3 hla, feVal_eq b b0 b1 b2 b3 hlb]
  have h3 : limbsVal u0 u1 u2 u3 + 2^256 * limbsVal u4 u5 u6 u7 =
      limbsVal8 u0 u1 u2 u3 u4 u5 u6 u7 := by
    unfold limbsVal limbsVal8
    ring
  rw [h3, huval] at hr_val
  exact hr_val

end PastaProofs
