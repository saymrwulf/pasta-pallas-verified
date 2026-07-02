/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/SubNegSpec.lean — subtraction and negation of the transpiled Fp.

   RUST ANALOG (src/fields/fp.rs):
   * `Fp::sub` (fp.rs:374-388): 4-limb sbb chain, then a conditional add-back
     of the modulus masked by the final borrow word (`MODULUS.0[i] & borrow`).
   * `Fp::neg` (fp.rs:405-...): computes p − a by a 4-limb sbb chain, then
     zeroes the result iff a = 0 (the `mask = −((a≠0) as u64)` trick).

   THE SUB SPEC IS DELIBERATELY MORE GENERAL THAN Canon × Canon:
     hypotheses   feVal b ≤ P   and   feVal a < feVal b + P
     conclusion   Canon r ∧ (r + b = a  ∨  r + b = a + P)     (exact ℕ)
   This covers the two call shapes in the crate:
     * canonical x, y (x < P ≤ y + P):     field subtraction;
     * `sub t MODULUS` with t < 2P:        the final conditional reduction of
       `add` and `montgomery_reduce` (t ≥ P → t − P; t < P → borrow, add-back
       gives t itself).
   The additive phrasing avoids ℕ-subtraction entirely; casting to 𝔽_p kills
   the +P branch ((P : 𝔽_p) = 0), giving ⟪r⟫ = ⟪a⟫ − ⟪b⟫.

   Imports: Proofs/HelperSpecs (adc/sbb/mac atoms).
   Imported by: AddSpec (add = adc chain ∘ sub · MODULUS), ReduceSpec
   (montgomery_reduce ends with the same call), ConstSpecs, FieldMain.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.HelperSpecs
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PastaProofs

open Aeneas.Std.WP

macro "dis" : tactic =>
  `(tactic| (subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac))

/-- The transpiled MODULUS constant, as a limb list. -/
theorem MODULUS_limbs :
    (↑fields.fp.MODULUS : List U64) =
      [11037532056220336129#u64, 2469829653914515739#u64, 0#u64,
       4611686018427387904#u64] := by
  unfold fields.fp.MODULUS
  rfl

/-- Its exact value is the Pallas prime. -/
theorem feVal_MODULUS : feVal fields.fp.MODULUS = P := by
  rw [feVal_eq _ _ _ _ _ MODULUS_limbs]
  unfold limbsVal P
  norm_num

/-- `Fp::sub`: exact two-case value identity + canonicity (see file header). -/
theorem sub_spec (a b : Fe) (hbP : feVal b ≤ P) (hab : feVal a < feVal b + P) :
    fields.fp.Fp.sub a b
      ⦃ r => Canon r ∧
             (feVal r + feVal b = feVal a ∨
              feVal r + feVal b = feVal a + P) ⦄ := by
  obtain ⟨a0, a1, a2, a3, hla⟩ := Fe.exists_limbs a
  obtain ⟨b0, b1, b2, b3, hlb⟩ := Fe.exists_limbs b
  rw [feVal_eq b b0 b1 b2 b3 hlb] at hbP
  rw [feVal_eq a a0 a1 a2 a3 hla, feVal_eq b b0 b1 b2 b3 hlb] at hab
  unfold fields.fp.Fp.sub
  -- ── limb reads + the 4-step sbb chain ────────────────────────────────────
  let* ⟨ i, hi ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i1, hi1 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d0, borrow0, hsb0 ⟩ ← sbb_spec by dis
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i3, hi3 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d1, borrow1, hsb1 ⟩ ← sbb_spec by dis
  let* ⟨ i4, hi4 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i5, hi5 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d2, borrow2, hsb2 ⟩ ← sbb_spec by dis
  let* ⟨ i6, hi6 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i7, hi7 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d3, borrow3, hsb3 ⟩ ← sbb_spec by dis
  -- ── conditional add-back: (MODULUS[i] & borrow) + adc chain ──────────────
  let* ⟨ i8, hi8 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i9, hi9, hi9bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ d01, carry0, hadc0 ⟩ ← adc_spec by dis
  let* ⟨ i10, hi10 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i11, hi11, hi11bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ d11, carry1, hadc1 ⟩ ← adc_spec by dis
  let* ⟨ i12, hi12 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i13, hi13, hi13bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ d21, carry2, hadc2 ⟩ ← adc_spec by dis
  let* ⟨ i14, hi14 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i15, hi15, hi15bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ d31, carry3, hadc3 ⟩ ← adc_spec by dis
  -- ── assemble ─────────────────────────────────────────────────────────────
  -- identify the reads with the named limbs / MODULUS literals
  -- val-level identifications of the reads (omega links through these)
  have hv_i : i.val = a0.val := by simp [hi, hla]
  have hv_i1 : i1.val = b0.val := by simp [hi1, hlb]
  have hv_i2 : i2.val = a1.val := by simp [hi2, hla]
  have hv_i3 : i3.val = b1.val := by simp [hi3, hlb]
  have hv_i4 : i4.val = a2.val := by simp [hi4, hla]
  have hv_i5 : i5.val = b2.val := by simp [hi5, hlb]
  have hv_i6 : i6.val = a3.val := by simp [hi6, hla]
  have hv_i7 : i7.val = b3.val := by simp [hi7, hlb]
  have hv_i8 : i8.val = 11037532056220336129 := by simp [hi8, MODULUS_limbs]
  have hv_i10 : i10.val = 2469829653914515739 := by simp [hi10, MODULUS_limbs]
  have hv_i12 : i12.val = 0 := by simp [hi12, MODULUS_limbs]
  have hv_i14 : i14.val = 4611686018427387904 := by simp [hi14, MODULUS_limbs]
  -- expose the ℕ-level land in the mask equations
  simp only [UScalar.val_and, hv_i8, hv_i10, hv_i12, hv_i14] at hi9 hi11 hi13 hi15
  -- limb bounds (make everything linear for omega)
  have hb_d0 : d0.val < 2^64 := by scalar_tac
  have hb_d1 : d1.val < 2^64 := by scalar_tac
  have hb_d2 : d2.val < 2^64 := by scalar_tac
  have hb_d3 : d3.val < 2^64 := by scalar_tac
  have hb_d01 : d01.val < 2^64 := by scalar_tac
  have hb_d11 : d11.val < 2^64 := by scalar_tac
  have hb_d21 : d21.val < 2^64 := by scalar_tac
  have hb_d31 : d31.val < 2^64 := by scalar_tac
  have hb_a0 : a0.val < 2^64 := by scalar_tac
  have hb_a1 : a1.val < 2^64 := by scalar_tac
  have hb_a2 : a2.val < 2^64 := by scalar_tac
  have hb_a3 : a3.val < 2^64 := by scalar_tac
  have hb_b0 : b0.val < 2^64 := by scalar_tac
  have hb_b1 : b1.val < 2^64 := by scalar_tac
  have hb_b2 : b2.val < 2^64 := by scalar_tac
  have hb_b3 : b3.val < 2^64 := by scalar_tac
  -- resolve the mask values in the two borrow3 cases
  rcases hsb3 with ⟨hbor3, hval3⟩ | ⟨hbor3, hval3⟩ <;>
    [ (simp only [hbor3, Nat.and_zero] at hi9 hi11 hi13 hi15);
      (simp only [hbor3, Nat.and_two_pow_sub_one_eq_mod] at hi9 hi11 hi13 hi15;
       norm_num at hi9 hi11 hi13 hi15) ] <;>
  · rw [feVal_eq a a0 a1 a2 a3 hla, feVal_eq b b0 b1 b2 b3 hlb]
    constructor
    · -- Canon: feVal r < P
      unfold Canon
      simp only [feVal_make]
      unfold limbsVal P at *
      trace_state
      omega
    · -- the two-case value identity
      simp only [feVal_make]
      unfold limbsVal P at *
      omega

/-- `Fp::neg`: total, canonical, and denotes −⟪a⟫ (for canonical input). -/
theorem neg_spec (a : Fe) (ha : Canon a) :
    fields.fp.Fp.neg a
      ⦃ r => Canon r ∧
             (feVal r + feVal a = P ∨ (feVal r = 0 ∧ feVal a = 0)) ⦄ := by
  obtain ⟨a0, a1, a2, a3, hla⟩ := Fe.exists_limbs a
  unfold Canon at ha
  rw [feVal_eq a a0 a1 a2 a3 hla] at ha
  unfold fields.fp.Fp.neg
  let* ⟨ i, hi ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i1, hi1 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d0, borrow0, hsb0 ⟩ ← sbb_spec by dis
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i3, hi3 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d1, borrow1, hsb1 ⟩ ← sbb_spec by dis
  let* ⟨ i4, hi4 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i5, hi5 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d2, borrow2, hsb2 ⟩ ← sbb_spec by dis
  let* ⟨ i6, hi6 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ i7, hi7 ⟩ ← Array.index_usize_spec by dis
  let* ⟨ d3, borrow3, hsb3 ⟩ ← sbb_spec by dis
  -- the is-zero test: i8 = a0 ||| a1, i9 = i8 ||| a2, i10 = i9 ||| a3
  let* ⟨ i8, hi8, hi8bv ⟩ ← UScalar.or_spec by dis
  let* ⟨ i9, hi9, hi9bv ⟩ ← UScalar.or_spec by dis
  let* ⟨ i10, hi10, hi10bv ⟩ ← UScalar.or_spec by dis
  let* ⟨ i11, hi11 ⟩ ← lift_spec by dis
  let* ⟨ mask, hmask ⟩ ← lift_spec by dis
  let* ⟨ i12, hi12, hi12bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ i13, hi13, hi13bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ i14, hi14, hi14bv ⟩ ← UScalar.and_spec by dis
  let* ⟨ i15, hi15, hi15bv ⟩ ← UScalar.and_spec by dis
  have hv_i : i.val = 11037532056220336129 := by simp [hi, MODULUS_limbs]
  have hv_i1 : i1.val = a0.val := by simp [hi1, hla]
  have hv_i2 : i2.val = 2469829653914515739 := by simp [hi2, MODULUS_limbs]
  have hv_i3 : i3.val = a1.val := by simp [hi3, hla]
  have hv_i4 : i4.val = 0 := by simp [hi4, MODULUS_limbs]
  have hv_i5 : i5.val = a2.val := by simp [hi5, hla]
  have hv_i6 : i6.val = 4611686018427387904 := by simp [hi6, MODULUS_limbs]
  have hv_i7 : i7.val = a3.val := by simp [hi7, hla]
  simp only [UScalar.val_or, hv_i1, hv_i3, hv_i5, hv_i7] at hi8 hi9 hi10
  simp only [UScalar.val_and] at hi12 hi13 hi14 hi15
  have hb_a0 : a0.val < 2^64 := by scalar_tac
  have hb_a1 : a1.val < 2^64 := by scalar_tac
  have hb_a2 : a2.val < 2^64 := by scalar_tac
  have hb_a3 : a3.val < 2^64 := by scalar_tac
  have hb_d0 : d0.val < 2^64 := by scalar_tac
  have hb_d1 : d1.val < 2^64 := by scalar_tac
  have hb_d2 : d2.val < 2^64 := by scalar_tac
  have hb_d3 : d3.val < 2^64 := by scalar_tac
  -- case: is the input zero?
  by_cases hz : a0.val = 0 ∧ a1.val = 0 ∧ a2.val = 0 ∧ a3.val = 0
  · -- a = 0: or-chain is 0, i11 = 1, mask = 0, result limbs all 0
    obtain ⟨h0, h1, h2, h3⟩ := hz
    have hor : i10.val = 0 := by
      simp [hi10, hi9, hi8, h0, h1, h2, h3]
    have hz10 : i10 = 0#u64 := by scalar_tac
    have h11 : i11.val = 1 := by
      subst hi11
      simp [hz10]
    have hm : mask.val = 0 := by
      subst hmask
      simp only [core.num.U64.wrapping_sub_val_eq]
      simp [h11, U64.size, U64.numBits_def]
    simp only [hm, Nat.and_zero] at hi12 hi13 hi14 hi15
    constructor
    · unfold Canon; simp only [feVal_make]; unfold limbsVal P; omega
    · right
      constructor
      · simp only [feVal_make]; unfold limbsVal; omega
      · rw [feVal_eq a a0 a1 a2 a3 hla]; unfold limbsVal; omega
  · -- a ≠ 0: or-chain nonzero, i11 = 0, mask = all-ones, result = p − a
    have hor : i10.val ≠ 0 := by
      rw [hi10, hi9, hi8]
      intro hcon
      apply hz
      have c1 := nat_or_eq_zero hcon
      have c2 := nat_or_eq_zero c1.1
      have c3 := nat_or_eq_zero c2.1
      exact ⟨c3.1, c3.2, c2.2, c1.2⟩
    have hz10 : ¬ (i10 = 0#u64) := by scalar_tac
    have h11 : i11.val = 0 := by
      subst hi11
      simp [hz10]
    have hm : mask.val = 2^64 - 1 := by
      subst hmask
      simp only [core.num.U64.wrapping_sub_val_eq]
      simp [h11, U64.size, U64.numBits_def]
    rw [hm] at hi12 hi13 hi14 hi15
    simp only [Nat.and_two_pow_sub_one_eq_mod] at hi12 hi13 hi14 hi15
    rw [Nat.mod_eq_of_lt hb_d0] at hi12
    rw [Nat.mod_eq_of_lt hb_d1] at hi13
    rw [Nat.mod_eq_of_lt hb_d2] at hi14
    rw [Nat.mod_eq_of_lt hb_d3] at hi15
    constructor
    · unfold Canon; simp only [feVal_make]; unfold limbsVal P at *; omega
    · left
      simp only [feVal_make, feVal_eq a a0 a1 a2 a3 hla]
      unfold limbsVal P at *
      omega

end PastaProofs
