/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ConstSpecs.lean — the transpiled constants are the right numbers.

   RUST ANALOG (src/fields/fp.rs): `MODULUS` (feVal_MODULUS lives in
   SubNegSpec.lean), `R = 2²⁵⁶ mod p` (Montgomery one), `R2 = 2⁵¹² mod p`,
   `INV = −p⁻¹ mod 2⁶⁴` (the Montgomery reduction multiplier), `zero`, `one`.

   Every proof here is kernel-checked literal arithmetic (norm_num on
   256/512-bit numerals — GMP-backed, milliseconds; NO native_decide).

   WHY THESE MATTER
   * `INV_spec` is THE hinge of montgomery_reduce: k = r·INV makes
     r + k·p ≡ 0 (mod 2⁶⁴) — each reduction round clears one limb exactly.
   * `R_val`/`one` give ⟪one⟫ = 1 (the denotation absorbs the R factor).
   * `R2_val` makes from_raw(x) = mont_mul(x, R2) denote x (used later for
     GENERATOR and the encode/surjectivity argument in FieldMain).
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.SubNegSpec
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 4000000

namespace PastaProofs

/-- R constant, as a limb list. -/
theorem R_limbs :
    (↑fields.fp.R : List U64) =
      [3780891978758094845#u64, 11037255111966004397#u64,
       18446744073709551615#u64, 4611686018427387903#u64] := by
  unfold fields.fp.R
  rfl

/-- feVal R = 2²⁵⁶ mod p (the Montgomery factor, reduced). -/
theorem feVal_R : feVal fields.fp.R = 2^256 % P := by
  rw [feVal_eq _ _ _ _ _ R_limbs]
  unfold limbsVal P
  norm_num

theorem R_canon : Canon fields.fp.R := by
  unfold Canon
  rw [feVal_R]
  unfold P
  norm_num

/-- R2 constant, as a limb list. -/
theorem R2_limbs :
    (↑fields.fp.R2 : List U64) =
      [10122100416058490895#u64, 15551789045973377255#u64,
       8617542898466512152#u64, 679271340751763220#u64] := by
  unfold fields.fp.R2
  rfl

/-- feVal R2 = 2⁵¹² mod p. -/
theorem feVal_R2 : feVal fields.fp.R2 = 2^512 % P := by
  rw [feVal_eq _ _ _ _ _ R2_limbs]
  unfold limbsVal P
  -- explicit division witness: 2⁵¹² = P·Q + R with R < P (norm_num checks the
  -- one big multiplication; omega concludes the mod identity)
  have hq : 28948022309329048855892746252171976963363056481941560715954676764349967630337 *
      463168356949264781694283940034751631412350973614059540860385843833705555034097 +
      4263855311831330276397237192126260515652039413828781833859739249380679483407 =
      13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
    norm_num
  have hpow : (2:ℕ)^512 =
      13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
    have hsplit : (2:ℕ)^512 = ((2:ℕ)^64)^8 := by
      rw [← pow_mul]
    rw [hsplit]
    norm_num
  rw [hpow]
  norm_num [hq]

theorem R2_canon : Canon fields.fp.R2 := by
  unfold Canon
  rw [feVal_R2]
  exact Nat.mod_lt _ (by unfold P; norm_num)

/-- INV is the Montgomery multiplier: INV · p ≡ −1 (mod 2⁶⁴). -/
theorem INV_spec : (fields.fp.INV.val * P + 1) % 2^64 = 0 := by
  unfold fields.fp.INV P
  norm_num

/-- `Fp::zero` runs and denotes 0 (canonically). -/
theorem zero_spec :
    fields.fp.Fp.zero ⦃ r => Canon r ∧ feVal r = 0 ⦄ := by
  unfold fields.fp.Fp.zero
  simp only [Aeneas.Std.WP.spec_ok]  -- ok (Array.repeat …)
  constructor
  · unfold Canon feVal
    simp [Array.repeat, List.replicate]
    unfold limbsVal P
    simp
  · unfold feVal
    simp [Array.repeat, List.replicate]
    unfold limbsVal
    simp

/-- `Fp::one` runs, is canonical, and its value is R mod p — so ⟪one⟫ = 1. -/
theorem one_spec :
    fields.fp.Fp.one ⦃ r => Canon r ∧ feVal r = 2^256 % P ⦄ := by
  unfold fields.fp.Fp.one
  simp only [Aeneas.Std.WP.spec_ok]
  exact ⟨R_canon, feVal_R⟩

/-- ⟪one⟫ = 1: the denotation cancels the Montgomery factor. -/
theorem one_denotes_one (r : Fe) (h : feVal r = 2^256 % P) : ⟪r⟫ = 1 := by
  unfold denote
  rw [h]
  have : ((2^256 % P : ℕ) : Fp) = (R : Fp) := by
    unfold R
    rw [ZMod.natCast_eq_natCast_iff']
    unfold P
    omega
  rw [this]
  exact R_mul_Rinv

end PastaProofs
