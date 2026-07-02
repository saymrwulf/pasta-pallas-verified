/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/ReduceSpec.lean — Montgomery reduction of the transpiled Fp.

   RUST ANALOG (src/fields/fp.rs:319-363, HAC Algorithm 14.32):
   4 rounds; round i computes k = rᵢ·INV mod 2⁶⁴ and adds k·p aligned at limb
   i (mac chain + carry into an adc), which makes limb i vanish — the mac's
   low output is DISCARDED because it is provably 0:
       rᵢ + k·p ≡ rᵢ·(1 + INV·p) ≡ 0  (mod 2⁶⁴)      [INV = −p⁻¹ mod 2⁶⁴]
   After 4 rounds the value is (t + m·p)/2²⁵⁶ for m = Σ kᵢ·2^(64i) < 2²⁵⁶,
   hence < 2P whenever t < 2²⁵⁶·P; the final `sub · MODULUS` (the general
   conditional reduction proven in SubNegSpec) lands it in [0, P).

   SPEC (multiplicative phrasing, no inverses over ℕ):
     t := limbsVal r0..r3 + 2²⁵⁶·limbsVal r4..r7 < 2²⁵⁶·P  →
     montgomery_reduce … = ok r  with  Canon r ∧ (feVal r·2²⁵⁶) % P = t % P
   — i.e. ⟪r⟫ = t·R⁻² in 𝔽_p wording is left to the callers (mul divides by
   one R via the denotation, the other via this congruence).

   MEMORY DISCIPLINE (post 2026-07-02 OOM): step side conditions are
   discharged by `scalar_tac` first (cheap), falling back to the simp-based
   discharge only if needed; per-round facts are established as small `have`s
   so no single tactic call sees an unbounded rewrite space.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ConstSpecs
import Mathlib.Tactic.LinearCombination
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PastaProofs

open Aeneas.Std.WP

macro "dix" : tactic =>
  `(tactic| scalar_tac)

/-- The four MODULUS limbs as named literals (readability of the rounds). -/
private def p0 : ℕ := 11037532056220336129
private def p1 : ℕ := 2469829653914515739
private def p2 : ℕ := 0
private def p3 : ℕ := 4611686018427387904
private def invLit : ℕ := 11037532056220336127

private theorem INV_val : fields.fp.INV.val = invLit := by
  unfold fields.fp.INV invLit
  rfl

/-- One Montgomery round drops a PROVABLY ZERO low limb:
    k = r·INV mod 2⁶⁴ makes r + k·p₀ ≡ r·(1 + INV·p₀) ≡ 0 (mod 2⁶⁴).
    Standalone so each instantiation carries a tiny proof term. -/
private theorem round_lo_zero (r k lo c z : ℕ)
    (hk : k = (r * invLit) % 2^64)
    (hm : lo + 2^64 * c = r + k * p0 + z) (hz : z = 0)
    (hb : lo < 2^64) : lo = 0 := by
  unfold invLit p0 at *
  omega

/-- THE ACCOUNTING LEMMA, context-free over plain ℕ (48 variables, the 20
    row equations of the 4 Montgomery rounds). Keeping it standalone keeps
    the kernel term of the main theorem small (the 2026-07-02 postmortem
    discipline: no giant certificates inside a 100-hypothesis context). -/
private theorem montgomery_rows_conclusion
    (r0 r1 r2 r3 r4 r5 r6 r7 k k1 k2 k3 : ℕ)
    (r11 r21 r31 r41 r22 r32 r42 r51 r33 r43 r52 r61 r44 r53 r62 r71 : ℕ)
    (c00 c01 c02 c03 c0e c10 c11 c12 c13 c1e : ℕ)
    (c20 c21 c22 c23 c2e c30 c31 c32 c33 c3e : ℕ)
    (hbound : r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3 +
        2^256 * (r4 + 2^64 * r5 + 2^128 * r6 + 2^192 * r7) < 2^256 * P)
    (hm00 : 0 + 2^64 * c00 = r0 + k * p0 + 0)
    (hm01 : r11 + 2^64 * c01 = r1 + k * p1 + c00)
    (hm02 : r21 + 2^64 * c02 = r2 + k * p2 + c01)
    (hm03 : r31 + 2^64 * c03 = r3 + k * p3 + c02)
    (ha0 : r41 + 2^64 * c0e = r4 + 0 + c03)
    (hm10 : 0 + 2^64 * c10 = r11 + k1 * p0 + 0)
    (hm11 : r22 + 2^64 * c11 = r21 + k1 * p1 + c10)
    (hm12 : r32 + 2^64 * c12 = r31 + k1 * p2 + c11)
    (hm13 : r42 + 2^64 * c13 = r41 + k1 * p3 + c12)
    (ha1 : r51 + 2^64 * c1e = r5 + c0e + c13)
    (hm20 : 0 + 2^64 * c20 = r22 + k2 * p0 + 0)
    (hm21 : r33 + 2^64 * c21 = r32 + k2 * p1 + c20)
    (hm22 : r43 + 2^64 * c22 = r42 + k2 * p2 + c21)
    (hm23 : r52 + 2^64 * c23 = r51 + k2 * p3 + c22)
    (ha2 : r61 + 2^64 * c2e = r6 + c1e + c23)
    (hm30 : 0 + 2^64 * c30 = r33 + k3 * p0 + 0)
    (hm31 : r44 + 2^64 * c31 = r43 + k3 * p1 + c30)
    (hm32 : r53 + 2^64 * c32 = r52 + k3 * p2 + c31)
    (hm33 : r62 + 2^64 * c33 = r61 + k3 * p3 + c32)
    (ha3 : r71 + 2^64 * c3e = r7 + c2e + c33)
    (hbk : k < 2^64) (hbk1 : k1 < 2^64) (hbk2 : k2 < 2^64) (hbk3 : k3 < 2^64)
    (hb44 : r44 < 2^64) (hb53 : r53 < 2^64) (hb62 : r62 < 2^64) (hb71 : r71 < 2^64) :
    (r44 + 2^64 * r53 + 2^128 * r62 + 2^192 * r71) < 2 * P ∧
    ((r44 + 2^64 * r53 + 2^128 * r62 + 2^192 * r71) * 2^256) % P =
      (r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3 +
       2^256 * (r4 + 2^64 * r5 + 2^128 * r6 + 2^192 * r7)) % P := by
  -- exact division identity with the final carry explicit
  -- (weights machine-derived offline: mac(i,j) ↦ 2^(64(i+j)), adc(i) ↦ 2^(64(i+4)))
  have hkey : (r44 + 2^64 * r53 + 2^128 * r62 + 2^192 * r71) * 2^256 +
      2^512 * c3e =
      (r0 + 2^64 * r1 + 2^128 * r2 + 2^192 * r3 +
       2^256 * (r4 + 2^64 * r5 + 2^128 * r6 + 2^192 * r7)) +
      (k + 2^64 * k1 + 2^128 * k2 + 2^192 * k3) * P := by
    unfold P p0 p1 p2 p3 at *
    omega
  have hc3e : c3e = 0 := by
    unfold P at hkey hbound
    omega
  rw [hc3e, Nat.mul_zero, Nat.add_zero] at hkey
  constructor
  · unfold P at hkey hbound ⊢
    omega
  · rw [hkey]
    exact Nat.add_mul_mod_self_right _ _ _

/-- Case-closing steps for the final congruence, standalone (context-free
    omega: the in-proof context confuses omega's preprocessing). -/
private theorem close_lo (x t' T M F : ℕ)
    (hv : x + M = t') (h2 : t' * F % M = T % M) :
    x * F % M = T % M := by
  have hx : x ≡ t' [MOD M] := by
    unfold Nat.ModEq
    rw [← hv]
    exact (Nat.add_mod_right x M).symm
  exact (hx.mul_right F).trans h2

private theorem close_hi (x t' T M F : ℕ)
    (hv : x + M = t' + M) (h2 : t' * F % M = T % M) :
    x * F % M = T % M := by
  have hx : x = t' := by omega
  rw [hx]
  exact h2

/-- The reduce postcondition, NAMED: the WP machinery carries this through
    all 41 steps of the body — as one small symbol instead of a term with
    78-digit literals (kernel-size discipline). -/
def MRPost (r0 r1 r2 r3 r4 r5 r6 r7 : U64) (r : Fe) : Prop :=
  Canon r ∧
  (feVal r * 2^256) % P =
    (limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7) % P


/-- The round-3-4 tail of `montgomery_reduce` (verbatim from the generated
    body), as its own definition so the proof can be split at the round
    boundary — a 41-`let*` monadic proof term overflows the Lean kernel's
    memory budget, but two ~20-op halves do not (SubNegSpec's 24-op chain is
    the empirical ceiling; see POSTMORTEM-2026-07-02). -/
def mont_tail (r22 r32 r42 r51 r6 r7 c1e : U64) : Result Fe := do
  let k2 ← lift (core.num.U64.wrapping_mul r22 fields.fp.INV)
  let i8 ← Array.index_usize fields.fp.MODULUS 0#usize
  let (_, carry8) ← arithmetic.fields.mac r22 k2 i8 0#u64
  let i9 ← Array.index_usize fields.fp.MODULUS 1#usize
  let (r33, carry9) ← arithmetic.fields.mac r32 k2 i9 carry8
  let i10 ← Array.index_usize fields.fp.MODULUS 2#usize
  let (r43, carry10) ← arithmetic.fields.mac r42 k2 i10 carry9
  let i11 ← Array.index_usize fields.fp.MODULUS 3#usize
  let (r52, carry11) ← arithmetic.fields.mac r51 k2 i11 carry10
  let (r61, carry23) ← arithmetic.fields.adc r6 c1e carry11
  let k3 ← lift (core.num.U64.wrapping_mul r33 fields.fp.INV)
  let i12 ← Array.index_usize fields.fp.MODULUS 0#usize
  let (_, carry12) ← arithmetic.fields.mac r33 k3 i12 0#u64
  let i13 ← Array.index_usize fields.fp.MODULUS 1#usize
  let (r44, carry13) ← arithmetic.fields.mac r43 k3 i13 carry12
  let i14 ← Array.index_usize fields.fp.MODULUS 2#usize
  let (r53, carry14) ← arithmetic.fields.mac r52 k3 i14 carry13
  let i15 ← Array.index_usize fields.fp.MODULUS 3#usize
  let (r62, carry15) ← arithmetic.fields.mac r61 k3 i15 carry14
  let (r71, _) ← arithmetic.fields.adc r7 carry23 carry15
  fields.fp.Fp.sub (Array.make 4#usize [ r44, r53, r62, r71 ]) fields.fp.MODULUS

/-- Rounds 3-4 + final reduction: given the round-1-2 accounting (as the input
    value `T`, the pre-round-3 limbs r22/r32/r42/r51 and their column
    identities), the tail lands the Montgomery result. -/
theorem mont_tail_spec (r0 r1 r2 r3 r4 r5 r6 r7 k k1 : U64)
    (r11 r21 r31 r41 r22 r32 r42 r51 : U64)
    (c00 c01 c02 c03 c0e c10 c11 c12 c13 c1e : U64)
    (hbound : limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7 < 2^256 * P)
    (hm00 : (0:ℕ) + 2^64 * c00.val = r0.val + k.val * p0 + 0)
    (hm01 : r11.val + 2^64 * c01.val = r1.val + k.val * p1 + c00.val)
    (hm02 : r21.val + 2^64 * c02.val = r2.val + k.val * p2 + c01.val)
    (hm03 : r31.val + 2^64 * c03.val = r3.val + k.val * p3 + c02.val)
    (ha0 : r41.val + 2^64 * c0e.val = r4.val + 0 + c03.val)
    (hm10 : (0:ℕ) + 2^64 * c10.val = r11.val + k1.val * p0 + 0)
    (hm11 : r22.val + 2^64 * c11.val = r21.val + k1.val * p1 + c10.val)
    (hm12 : r32.val + 2^64 * c12.val = r31.val + k1.val * p2 + c11.val)
    (hm13 : r42.val + 2^64 * c13.val = r41.val + k1.val * p3 + c12.val)
    (ha1 : r51.val + 2^64 * c1e.val = r5.val + c0e.val + c13.val)
    (hbk : k.val < 2^64) (hbk1 : k1.val < 2^64) :
    mont_tail r22 r32 r42 r51 r6 r7 c1e
      ⦃ r => MRPost r0 r1 r2 r3 r4 r5 r6 r7 r ⦄ := by
  unfold mont_tail
  -- round 3
  let* ⟨ k2, hk2 ⟩ ← lift_spec by dix
  let* ⟨ i8, hi8 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ lo2, c20, hm20 ⟩ ← mac_spec by dix
  let* ⟨ i9, hi9 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r33, c21, hm21 ⟩ ← mac_spec by dix
  let* ⟨ i10, hi10 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r43, c22, hm22 ⟩ ← mac_spec by dix
  let* ⟨ i11, hi11 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r52, c23, hm23 ⟩ ← mac_spec by dix
  let* ⟨ r61, c2e, ha2 ⟩ ← adc_spec by dix
  -- round 4
  let* ⟨ k3, hk3 ⟩ ← lift_spec by dix
  let* ⟨ i12, hi12 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ lo3, c30, hm30 ⟩ ← mac_spec by dix
  let* ⟨ i13, hi13 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r44, c31, hm31 ⟩ ← mac_spec by dix
  let* ⟨ i14, hi14 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r53, c32, hm32 ⟩ ← mac_spec by dix
  let* ⟨ i15, hi15 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r62, c33, hm33 ⟩ ← mac_spec by dix
  let* ⟨ r71, c3e, ha3 ⟩ ← adc_spec by dix
  -- MODULUS reads
  have hp_i8 : i8.val = p0 := by simp [hi8, MODULUS_limbs, p0]
  have hp_i9 : i9.val = p1 := by simp [hi9, MODULUS_limbs, p1]
  have hp_i10 : i10.val = p2 := by simp [hi10, MODULUS_limbs, p2]
  have hp_i11 : i11.val = p3 := by simp [hi11, MODULUS_limbs, p3]
  have hp_i12 : i12.val = p0 := by simp [hi12, MODULUS_limbs, p0]
  have hp_i13 : i13.val = p1 := by simp [hi13, MODULUS_limbs, p1]
  have hp_i14 : i14.val = p2 := by simp [hi14, MODULUS_limbs, p2]
  have hp_i15 : i15.val = p3 := by simp [hi15, MODULUS_limbs, p3]
  have hkv2 : k2.val = (r22.val * invLit) % 2^64 := by
    subst hk2; simp [INV_val, U64.size, U64.numBits_def]
  have hkv3 : k3.val = (r33.val * invLit) % 2^64 := by
    subst hk3; simp [INV_val, U64.size, U64.numBits_def]
  have hb_lo2 : lo2.val < 2^64 := by scalar_tac
  have hb_lo3 : lo3.val < 2^64 := by scalar_tac
  rw [hp_i8] at hm20
  have hlo2 : lo2.val = 0 := round_lo_zero _ _ _ _ _ hkv2 hm20 rfl hb_lo2
  rw [hp_i12] at hm30
  have hlo3 : lo3.val = 0 := round_lo_zero _ _ _ _ _ hkv3 hm30 rfl hb_lo3
  rw [hlo2] at hm20
  rw [hlo3] at hm30
  have hb_r44 : r44.val < 2^64 := by scalar_tac
  have hb_r53 : r53.val < 2^64 := by scalar_tac
  have hb_r62 : r62.val < 2^64 := by scalar_tac
  have hb_r71 : r71.val < 2^64 := by scalar_tac
  have hb_k2 : k2.val < 2^64 := by scalar_tac
  have hb_k3 : k3.val < 2^64 := by scalar_tac
  rw [hp_i9] at hm21; rw [hp_i10] at hm22; rw [hp_i11] at hm23
  rw [hp_i13] at hm31; rw [hp_i14] at hm32; rw [hp_i15] at hm33
  try clear hi8
  try clear hi9
  try clear hi10
  try clear hi11
  try clear hi12
  try clear hi13
  try clear hi14
  try clear hi15
  try clear hp_i8
  try clear hp_i9
  try clear hp_i10
  try clear hp_i11
  try clear hp_i12
  try clear hp_i13
  try clear hp_i14
  try clear hp_i15
  try clear hk2
  try clear hk3
  try clear hkv2
  try clear hkv3
  try clear hlo2
  try clear hlo3
  try clear hb_lo2
  try clear hb_lo3
  have hbound' : r0.val + 2^64 * r1.val + 2^128 * r2.val + 2^192 * r3.val +
      2^256 * (r4.val + 2^64 * r5.val + 2^128 * r6.val + 2^192 * r7.val) <
      2^256 * P := by
    unfold limbsVal at hbound
    exact hbound
  have hfin := montgomery_rows_conclusion
    r0.val r1.val r2.val r3.val r4.val r5.val r6.val r7.val
    k.val k1.val k2.val k3.val
    r11.val r21.val r31.val r41.val r22.val r32.val r42.val r51.val
    r33.val r43.val r52.val r61.val r44.val r53.val r62.val r71.val
    c00.val c01.val c02.val c03.val c0e.val c10.val c11.val c12.val c13.val c1e.val
    c20.val c21.val c22.val c23.val c2e.val c30.val c31.val c32.val c33.val c3e.val
    hbound' hm00 hm01 hm02 hm03 ha0 hm10 hm11 hm12 hm13 ha1
    hm20 hm21 hm22 hm23 ha2 hm30 hm31 hm32 hm33 ha3
    hbk hbk1 hb_k2 hb_k3 hb_r44 hb_r53 hb_r62 hb_r71
  clear hm00 hm01 hm02 hm03 hm10 hm11 hm12 hm13
        hm20 hm21 hm22 hm23 hm30 hm31 hm32 hm33 ha0 ha1 ha2 ha3
  have hMle : feVal fields.fp.MODULUS ≤ P := le_of_eq feVal_MODULUS
  have hdlt : feVal (Array.make 4#usize [r44, r53, r62, r71] (by simp)) <
      feVal fields.fp.MODULUS + P := by
    rw [feVal_MODULUS, feVal_make]
    unfold limbsVal
    exact lt_of_lt_of_le hfin.1 (by omega)
  let* ⟨ r, hr_canon, hr_val ⟩ ← sub_spec by
    (first | exact hMle | exact hdlt)
  unfold MRPost
  refine ⟨hr_canon, ?_⟩
  rw [feVal_MODULUS, feVal_make] at hr_val
  have h2 := hfin.2
  unfold limbsVal at hr_val ⊢
  rcases hr_val with hv | hv
  · exact close_lo _ _ _ _ _ hv h2
  · exact close_hi _ _ _ _ _ hv h2

/-- `montgomery_reduce`: total, canonical, and r·R ≡ t (mod p) — see header. -/
theorem montgomery_reduce_spec (r0 r1 r2 r3 r4 r5 r6 r7 : U64)
    (hbound : limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7 < 2^256 * P) :
    fields.fp.Fp.montgomery_reduce r0 r1 r2 r3 r4 r5 r6 r7
      ⦃ r => MRPost r0 r1 r2 r3 r4 r5 r6 r7 r ⦄ := by
  unfold fields.fp.Fp.montgomery_reduce
  -- ── rounds 1-2 only (rounds 3-4 + reduction are mont_tail_spec) ───────────
  let* ⟨ k, hk ⟩ ← lift_spec by dix
  let* ⟨ i, hi ⟩ ← Array.index_usize_spec by dix
  let* ⟨ lo0, c00, hm00 ⟩ ← mac_spec by dix
  let* ⟨ i1, hi1 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r11, c01, hm01 ⟩ ← mac_spec by dix
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r21, c02, hm02 ⟩ ← mac_spec by dix
  let* ⟨ i3, hi3 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r31, c03, hm03 ⟩ ← mac_spec by dix
  let* ⟨ r41, c0e, ha0 ⟩ ← adc_spec by dix
  let* ⟨ k1, hk1 ⟩ ← lift_spec by dix
  let* ⟨ i4, hi4 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ lo1, c10, hm10 ⟩ ← mac_spec by dix
  let* ⟨ i5, hi5 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r22, c11, hm11 ⟩ ← mac_spec by dix
  let* ⟨ i6, hi6 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r32, c12, hm12 ⟩ ← mac_spec by dix
  let* ⟨ i7, hi7 ⟩ ← Array.index_usize_spec by dix
  let* ⟨ r42, c13, hm13 ⟩ ← mac_spec by dix
  let* ⟨ r51, c1e, ha1 ⟩ ← adc_spec by dix
  -- identify the modulus reads / k for the tail's hypotheses
  have hp_i : i.val = p0 := by simp [hi, MODULUS_limbs, p0]
  have hp_i1 : i1.val = p1 := by simp [hi1, MODULUS_limbs, p1]
  have hp_i2 : i2.val = p2 := by simp [hi2, MODULUS_limbs, p2]
  have hp_i3 : i3.val = p3 := by simp [hi3, MODULUS_limbs, p3]
  have hp_i4 : i4.val = p0 := by simp [hi4, MODULUS_limbs, p0]
  have hp_i5 : i5.val = p1 := by simp [hi5, MODULUS_limbs, p1]
  have hp_i6 : i6.val = p2 := by simp [hi6, MODULUS_limbs, p2]
  have hp_i7 : i7.val = p3 := by simp [hi7, MODULUS_limbs, p3]
  have hbk : k.val < 2^64 := by scalar_tac
  have hbk1 : k1.val < 2^64 := by scalar_tac
  rw [hp_i] at hm00; rw [hp_i1] at hm01; rw [hp_i2] at hm02; rw [hp_i3] at hm03
  rw [hp_i4] at hm10; rw [hp_i5] at hm11; rw [hp_i6] at hm12; rw [hp_i7] at hm13
  -- the tail carries the full result
  exact mont_tail_spec r0 r1 r2 r3 r4 r5 r6 r7 k k1
    r11 r21 r31 r41 r22 r32 r42 r51
    c00 c01 c02 c03 c0e c10 c11 c12 c13 c1e
    hbound hm00 hm01 hm02 hm03 ha0 hm10 hm11 hm12 hm13 ha1 hbk hbk1

end PastaProofs
