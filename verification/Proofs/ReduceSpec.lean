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
open Aeneas Aeneas.Std Result
open pasta_curves

set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PastaProofs

open Aeneas.Std.WP

macro "dix" : tactic =>
  `(tactic| (first | scalar_tac | (subst_vars; simp [Array.set_val_eq, *]; scalar_tac)))

/-- The four MODULUS limbs as named literals (readability of the rounds). -/
private def p0 : ℕ := 11037532056220336129
private def p1 : ℕ := 2469829653914515739
private def p2 : ℕ := 0
private def p3 : ℕ := 4611686018427387904
private def invLit : ℕ := 11037532056220336127

private theorem INV_val : fields.fp.INV.val = invLit := by
  unfold fields.fp.INV invLit
  rfl

/-- `montgomery_reduce`: total, canonical, and r·R ≡ t (mod p) — see header. -/
theorem montgomery_reduce_spec (r0 r1 r2 r3 r4 r5 r6 r7 : U64)
    (hbound : limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7 < 2^256 * P) :
    fields.fp.Fp.montgomery_reduce r0 r1 r2 r3 r4 r5 r6 r7
      ⦃ r => Canon r ∧
             (feVal r * 2^256) % P =
               (limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7) % P ⦄ := by
  unfold fields.fp.Fp.montgomery_reduce
  -- ── round 1 (clears limb 0) ───────────────────────────────────────────────
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
  -- ── round 2 (clears limb 1) ───────────────────────────────────────────────
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
  -- ── round 3 (clears limb 2) ───────────────────────────────────────────────
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
  -- ── round 4 (clears limb 3) ───────────────────────────────────────────────
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
  -- ── identifications: MODULUS reads and k values ───────────────────────────
  have hp_i : i.val = p0 := by simp [hi, MODULUS_limbs, p0]
  have hp_i1 : i1.val = p1 := by simp [hi1, MODULUS_limbs, p1]
  have hp_i2 : i2.val = p2 := by simp [hi2, MODULUS_limbs, p2]
  have hp_i3 : i3.val = p3 := by simp [hi3, MODULUS_limbs, p3]
  have hp_i4 : i4.val = p0 := by simp [hi4, MODULUS_limbs, p0]
  have hp_i5 : i5.val = p1 := by simp [hi5, MODULUS_limbs, p1]
  have hp_i6 : i6.val = p2 := by simp [hi6, MODULUS_limbs, p2]
  have hp_i7 : i7.val = p3 := by simp [hi7, MODULUS_limbs, p3]
  have hp_i8 : i8.val = p0 := by simp [hi8, MODULUS_limbs, p0]
  have hp_i9 : i9.val = p1 := by simp [hi9, MODULUS_limbs, p1]
  have hp_i10 : i10.val = p2 := by simp [hi10, MODULUS_limbs, p2]
  have hp_i11 : i11.val = p3 := by simp [hi11, MODULUS_limbs, p3]
  have hp_i12 : i12.val = p0 := by simp [hi12, MODULUS_limbs, p0]
  have hp_i13 : i13.val = p1 := by simp [hi13, MODULUS_limbs, p1]
  have hp_i14 : i14.val = p2 := by simp [hi14, MODULUS_limbs, p2]
  have hp_i15 : i15.val = p3 := by simp [hi15, MODULUS_limbs, p3]
  have hkv : k.val = (r0.val * invLit) % 2^64 := by
    subst hk; simp [INV_val, U64.size, U64.numBits_def]
  have hkv1 : k1.val = (r11.val * invLit) % 2^64 := by
    subst hk1; simp [INV_val, U64.size, U64.numBits_def]
  have hkv2 : k2.val = (r22.val * invLit) % 2^64 := by
    subst hk2; simp [INV_val, U64.size, U64.numBits_def]
  have hkv3 : k3.val = (r33.val * invLit) % 2^64 := by
    subst hk3; simp [INV_val, U64.size, U64.numBits_def]
  -- ── the dropped low limbs are 0 (the whole point of k = r·INV) ────────────
  have hb_lo0 : lo0.val < 2^64 := by scalar_tac
  have hb_lo1 : lo1.val < 2^64 := by scalar_tac
  have hb_lo2 : lo2.val < 2^64 := by scalar_tac
  have hb_lo3 : lo3.val < 2^64 := by scalar_tac
  have hlo0 : lo0.val = 0 := by
    rw [hp_i] at hm00; unfold p0 invLit at *; omega
  have hlo1 : lo1.val = 0 := by
    rw [hp_i4] at hm10; unfold p0 invLit at *; omega
  have hlo2 : lo2.val = 0 := by
    rw [hp_i8] at hm20; unfold p0 invLit at *; omega
  have hlo3 : lo3.val = 0 := by
    rw [hp_i12] at hm30; unfold p0 invLit at *; omega
  -- ── the pre-reduction value t' = (t + m·p)/2²⁵⁶ < 2P ─────────────────────
  have hb_r44 : r44.val < 2^64 := by scalar_tac
  have hb_r53 : r53.val < 2^64 := by scalar_tac
  have hb_r62 : r62.val < 2^64 := by scalar_tac
  have hb_r71 : r71.val < 2^64 := by scalar_tac
  have hb_k : k.val < 2^64 := by scalar_tac
  have hb_k1 : k1.val < 2^64 := by scalar_tac
  have hb_k2 : k2.val < 2^64 := by scalar_tac
  have hb_k3 : k3.val < 2^64 := by scalar_tac
  -- exact division identity: t'·2²⁵⁶ = t + m·p  (all mac/adc rows summed)
  have hkey : limbsVal r44 r53 r62 r71 * 2^256 =
      (limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7) +
      (k.val + 2^64 * k1.val + 2^128 * k2.val + 2^192 * k3.val) * P := by
    rw [hp_i1, hp_i2, hp_i3] at hm01 hm02 hm03
    rw [hp_i5, hp_i6, hp_i7] at hm11 hm12 hm13
    rw [hp_i9, hp_i10, hp_i11] at hm21 hm22 hm23
    rw [hp_i13, hp_i14, hp_i15] at hm31 hm32 hm33
    rw [hp_i] at hm00; rw [hp_i4] at hm10; rw [hp_i8] at hm20; rw [hp_i12] at hm30
    unfold limbsVal P p0 p1 p2 p3 at *
    omega
  have ht' : limbsVal r44 r53 r62 r71 < 2 * P := by
    unfold limbsVal P at *
    omega
  -- ── final conditional reduction ───────────────────────────────────────────
  have hMle : feVal fields.fp.MODULUS ≤ P := le_of_eq feVal_MODULUS
  have hdlt : feVal (Array.make 4#usize [r44, r53, r62, r71] (by simp)) <
      feVal fields.fp.MODULUS + P := by
    rw [feVal_MODULUS, feVal_make]
    omega
  let* ⟨ r, hr_canon, hr_val ⟩ ← sub_spec by
    (first | exact hMle | exact hdlt)
  refine ⟨hr_canon, ?_⟩
  rw [feVal_MODULUS, feVal_make] at hr_val
  -- feVal r ∈ {t', t' − P}; both give feVal r·2²⁵⁶ ≡ t (mod P) via hkey
  unfold Canon at hr_canon
  rcases hr_val with hv | hv
  · -- feVal r + P = t'  … wait: hv : feVal r + P = t' ∨ feVal r = t' — see below
    -- (sub_spec: r + b = a): here b = P, a = t' → feVal r + P = t'
    have : (feVal r + P) * 2^256 =
        (limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7) +
        (k.val + 2^64 * k1.val + 2^128 * k2.val + 2^192 * k3.val) * P := by
      rw [hv]; exact hkey
    unfold limbsVal P at *
    omega
  · -- feVal r + P = t' + P → feVal r = t'
    have : (feVal r + P) * 2^256 =
        ((limbsVal r0 r1 r2 r3 + 2^256 * limbsVal r4 r5 r6 r7) +
        (k.val + 2^64 * k1.val + 2^128 * k2.val + 2^192 * k3.val) * P) + P * 2^256 := by
      rw [hv]
      rw [← hkey]
      ring
    unfold limbsVal P at *
    omega

end PastaProofs
