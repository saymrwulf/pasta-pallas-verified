/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/Denote.lean — the SEMANTIC FOUNDATION: from machine limbs to 𝔽_p
   (Pallas base field), MONTGOMERY FORM.

   WHAT THIS FILE PROVIDES
   * `P`, `Fp := ZMod P` — the Pallas modulus (primality from Proofs/PPallas.lean)
   * `Fe := fields.fp.Fp` — the transpiled element type: 4 little-endian u64
     limbs (`Array Std.U64 4`)
   * `limbsVal`/`feVal` — the EXACT natural-number value Σ lᵢ·2^(64i)
   * `R`, `Rinv` — the Montgomery factor 2²⁵⁶ and its inverse in 𝔽_p
   * `denote` (⟪·⟫)  — THE DENOTATION: ⟪a⟫ = feVal a · R⁻¹  ∈ 𝔽_p.
     pasta_curves stores a·R mod p; dividing by R in the denotation makes
     every proof statement live in plain 𝔽_p (⟪mul a b⟫ = ⟪a⟫·⟪b⟫ with NO
     R-factor bookkeeping at the spec level).
   * `Canon` — the representation invariant: feVal a < P.  Unlike dalek's
     radix-51 code (loose 2⁵²/2⁵⁴ bounds), pasta_curves keeps every element
     STRICTLY REDUCED: each op ends with a conditional subtraction of p.
   * `Fe.exists_limbs` — the destructuring device every proof starts with.

   RUST ANALOG: src/fields/fp.rs — `pub struct Fp(pub(crate) [u64; 4])`,
   invariant documented at the type: "little-endian bit order; values are
   always in Montgomery form aR mod p, with the reduced representative".

   Imports: gen/PallasFp (the transpiled code), Proofs/PPallas (primality).
   Imported by: every other proof file.
   ────────────────────────────────────────────────────────────────────────────── -/
import PallasFp.Funs
import Proofs.PPallas
open Aeneas Aeneas.Std Result
open pasta_curves

namespace PastaProofs

/-- The Pallas base-field modulus
    p = 2²⁵⁴ + 45560315531419706090280762371685220353. -/
def P : ℕ := 28948022309329048855892746252171976963363056481941560715954676764349967630337

theorem P_prime : Nat.Prime P := pallas_prime

instance : Fact (Nat.Prime P) := ⟨P_prime⟩

/-- 𝔽_p as mathlib's `ZMod P` — a `Field` because `P` is prime. -/
abbrev Fp := ZMod P

/-- The transpiled element type: 4 little-endian u64 limbs. -/
abbrev Fe := fields.fp.Fp

/-- Exact ℕ value of 4 little-endian u64 limbs. -/
def limbsVal (a0 a1 a2 a3 : U64) : ℕ :=
  a0.val + 2^64 * a1.val + 2^128 * a2.val + 2^192 * a3.val

/-- Exact ℕ value of an `Fe`. -/
def feVal (a : Fe) : ℕ :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3] => limbsVal a0 a1 a2 a3
  | _ => 0

/-- Every `Fe` IS four named u64 limbs. -/
theorem Fe.exists_limbs (a : Fe) :
    ∃ a0 a1 a2 a3 : U64, (↑a : List U64) = [a0, a1, a2, a3] := by
  obtain ⟨l, hl⟩ := a
  match l, hl with
  | [a0, a1, a2, a3], _ => exact ⟨a0, a1, a2, a3, rfl⟩

/-- Once limbs are named, `feVal` unfolds to the polynomial. -/
@[simp]
theorem feVal_eq (a : Fe) (a0 a1 a2 a3 : U64)
    (h : (↑a : List U64) = [a0, a1, a2, a3]) :
    feVal a = limbsVal a0 a1 a2 a3 := by
  unfold feVal; rw [h]

/-- feVal of a literal `Array.make` — the form the generated code produces
    (the length side condition `h` is quantified so simp matches any proof). -/
@[simp]
theorem feVal_make (a0 a1 a2 a3 : U64) (h) :
    feVal (Array.make 4#usize [a0, a1, a2, a3] h) = limbsVal a0 a1 a2 a3 := rfl

/-- Any `Fe` value is < 2²⁵⁶ (four u64 limbs). -/
theorem feVal_lt (a : Fe) : feVal a < 2^256 := by
  obtain ⟨a0, a1, a2, a3, hl⟩ := Fe.exists_limbs a
  rw [feVal_eq a a0 a1 a2 a3 hl]
  unfold limbsVal
  scalar_tac

/-- The representation invariant: strictly reduced (value below the modulus).
    Every constructor/operation of the crate maintains this. -/
def Canon (a : Fe) : Prop := feVal a < P

/-- The Montgomery factor. -/
def R : ℕ := 2^256

/-- P is odd (in particular ≠ 2), so 2 — hence R = 2²⁵⁶ — is a unit mod P. -/
theorem two_ne_zero_fp : (2 : Fp) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : Fp).val = 2 :=
    ZMod.val_cast_of_lt (by norm_num [P])
  rw [show ((2:ℕ):Fp) = (2:Fp) by push_cast; ring, h, ZMod.val_zero] at h2
  norm_num at h2

theorem R_ne_zero : (R : Fp) ≠ 0 := by
  have hR : (R : Fp) = (2 : Fp)^256 := by unfold R; push_cast; ring
  rw [hR]
  exact pow_ne_zero 256 two_ne_zero_fp

/-- R⁻¹ in 𝔽_p (field inverse; noncomputable, spec-level only). -/
noncomputable def Rinv : Fp := (R : Fp)⁻¹

theorem R_mul_Rinv : (R : Fp) * Rinv = 1 :=
  mul_inv_cancel₀ R_ne_zero

theorem Rinv_mul_R : Rinv * (R : Fp) = 1 := by
  rw [mul_comm]; exact R_mul_Rinv

theorem Rinv_ne_zero : Rinv ≠ 0 := by
  intro h
  have := R_mul_Rinv
  rw [h, mul_zero] at this
  exact one_ne_zero this.symm

/-- THE DENOTATION: machine limbs ↦ 𝔽_p, absorbing the Montgomery factor. -/
noncomputable def denote (a : Fe) : Fp := (feVal a : Fp) * Rinv

notation "⟪" a "⟫" => denote a

/-- Two canonical representatives with equal denotation are limb-identical
    in value: ⟪·⟫ is injective on `Canon`. -/
theorem denote_inj (a b : Fe) (ha : Canon a) (hb : Canon b)
    (h : ⟪a⟫ = ⟪b⟫) : feVal a = feVal b := by
  unfold denote at h
  have h' : (feVal a : Fp) = (feVal b : Fp) :=
    mul_right_cancel₀ Rinv_ne_zero h
  have := (ZMod.natCast_eq_natCast_iff' (feVal a) (feVal b) P).mp h'
  unfold Canon at ha hb
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Congruence mod P transfers to equal denotations. -/
theorem denote_eq_of_feVal_congr (a b : Fe)
    (h : feVal a % P = feVal b % P) : ⟪a⟫ = ⟪b⟫ := by
  unfold denote
  congr 1
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h

end PastaProofs
