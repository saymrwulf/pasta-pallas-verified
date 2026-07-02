/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/HelperSpecs.lean — exact specs for the u64 carry primitives
   adc / sbb / mac (src/arithmetic/fields.rs), TRANSPILED TRANSPARENTLY.

   These three ~5-line const fns are the atoms of every Pallas field op:
   * adc a b c   = (lo, hi)  with  lo + 2⁶⁴·hi = a + b + c           (exact ℕ)
   * mac a b c d = (lo, hi)  with  lo + 2⁶⁴·hi = a + b·c + d         (exact ℕ)
   * sbb a b bor = (d, bor') with  d + b + ⌊bor/2⁶³⌋ = a + 2⁶⁴·β'
                   where bor' ∈ {0, 2⁶⁴−1} and β' = (bor' ≠ 0)       (exact ℕ)
     (sbb consumes only the TOP BIT of the incoming borrow word and produces
      an all-ones/all-zeros borrow word — exactly the Rust convention:
      `let (_, borrow) = sbb(..)` then `mask & borrow` and `borrow >> 63`.)

   The u128 intermediates cannot overflow: a + b + c ≤ 3·(2⁶⁴−1) < 2¹²⁸ and
   a + b·c + d ≤ (2⁶⁴−1) + (2⁶⁴−1)² + (2⁶⁴−1) < 2¹²⁸ — proved, not assumed.

   Every lemma is `@[step]`-registered so the op proofs consume adc/sbb/mac
   calls in one `let*` step each.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.Denote
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 4000000

namespace PastaProofs

open Aeneas.Std.WP

/-- Generic step rule for `lift` of a pure computation: the result IS the
    expression (the @[simp] val-lemmas of the Aeneas library then evaluate it). -/
@[step]
theorem lift_spec {α : Type u} (x : α) : lift x ⦃ y => y = x ⦄ := by
  simp [lift]

/-- `x ||| y = 0` forces both to be zero (bitwise). -/
theorem nat_or_eq_zero {x y : ℕ} (h : x ||| y = 0) : x = 0 ∧ y = 0 := by
  constructor <;> {
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun n => n.testBit i) h
    simp [Nat.testBit_or] at this
    simp [this]
  }

/-- Discharge tactic shared by the steps (same as the ed25519 repos). -/
macro "dis" : tactic =>
  `(tactic| (subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac))

/-- `adc a b carry = (lo, hi)` with `lo + 2⁶⁴·hi = a + b + carry` (exact). -/
@[step]
theorem adc_spec (a b c : U64) :
    arithmetic.fields.adc a b c
      ⦃ p => p.1.val + 2^64 * p.2.val = a.val + b.val + c.val ∧
             p.2.val ≤ 2 ⦄ := by
  unfold arithmetic.fields.adc
  have ha : a.val < 2^64 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hc : c.val < 2^64 := by scalar_tac
  step* by dis
  -- lo = (a+b+c) mod 2⁶⁴, hi = (a+b+c) / 2⁶⁴: exact split of a 128-bit sum
  simp_all [UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `mac a b c carry = (lo, hi)` with `lo + 2⁶⁴·hi = a + b·c + carry` (exact). -/
@[step]
theorem mac_spec (a b c d : U64) :
    arithmetic.fields.mac a b c d
      ⦃ p => p.1.val + 2^64 * p.2.val = a.val + b.val * c.val + d.val ⦄ := by
  unfold arithmetic.fields.mac
  have ha : a.val < 2^64 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hc : c.val < 2^64 := by scalar_tac
  have hd : d.val < 2^64 := by scalar_tac
  have hbc : b.val * c.val ≤ (2^64-1) * (2^64-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  step* by dis
  simp_all [UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `sbb a b borrow = (d, borrow')`:
    * only the top bit β = ⌊borrow/2⁶³⌋ of the incoming borrow is consumed;
    * `d + b + β = a + 2⁶⁴·β'` exactly, where β' ∈ {0,1} flags the borrow-out;
    * the outgoing borrow WORD is 0 or all-ones (β' spread over 64 bits) —
      the shape `mask & borrow` arithmetic downstream depends on. -/
@[step]
theorem sbb_spec (a b bor : U64) :
    arithmetic.fields.sbb a b bor
      ⦃ p => (p.2.val = 0 ∧ p.1.val + b.val + bor.val / 2^63 = a.val) ∨
             (p.2.val = 2^64 - 1 ∧
              p.1.val + b.val + bor.val / 2^63 = a.val + 2^64) ⦄ := by
  unfold arithmetic.fields.sbb
  have ha : a.val < 2^64 := by scalar_tac
  have hb : b.val < 2^64 := by scalar_tac
  have hbor : bor.val < 2^64 := by scalar_tac
  have hβ : bor.val / 2^63 ≤ 1 := by omega
  step* by dis
  -- the wrapping u128 subtraction: ret = (a − b − β) mod 2¹²⁸;
  -- d = ret mod 2⁶⁴, borrow' = (ret >>> 64) mod 2⁶⁴
  simp_all [UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow,
            UScalar.size, U128.size, U64.size, U128.numBits_def, U64.numBits_def]
  omega

end PastaProofs
