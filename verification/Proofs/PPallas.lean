/-
═══════════════════════════════════════════════════════════════════════════════
Proofs/PPallas.lean — primality of the Pallas (Pasta) base-field modulus
  p = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
═══════════════════════════════════════════════════════════════════════════════

WHAT THIS FILE PROVES
  `pallas_prime : Nat.Prime P` where P is the 255-bit modulus of the Pallas
  curve base field F_p.  Axiom-free Lucas/Pratt certificate.

CERTIFICATE TREE (p−1 factorization, leaves first)
  p − 1 = 2³² · 3 · 463 · f1 · f2
    where f1 = 539204044132271846773       (69 bits)
          f2 = 8999194758858563409123804352480028797519453   (143 bits)

  f1 − 1 = 2² · 3⁵ · 89 · 14923 · 417677162933
  f2 − 1 = 2² · 3⁴ · 11 · 2531 · 115603 · 1197907 · 22160661629 · 325086459374267

  Sub-leaves (all norm_num-certifiable):
    417677162933 − 1 = 2² · 59 · 1973 · 897019
    22160661629  − 1 = 2² · 7 · 19 · 41655379
    14923        − 1 = 2 · 3² · 829
    115603       − 1 = 2 · 3 · 19267
    1197907      − 1 = 2 · 3 · 53 · 3767
    325086459374267 − 1 = 2 · 509 · 413527 · 772231
    463          − 1 = 2 · 3 · 7 · 11
    2531         − 1 = 2 · 5 · 11 · 23
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace PPallas

-- ═════════════════════════════════════════════════════════════════════════════
-- Kernel-checkable modular exponentiation
-- ═════════════════════════════════════════════════════════════════════════════

/-- Fuel-based binary modular exponentiation, kernel-reducible (GMP-fast `decide`).

MATH (for sufficient fuel; made precise by `powModAux_eq`):
  `powModAux fuel a k n = a^k mod n`.
Algorithm: square-and-multiply on binary digits of k. -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, n => 1 % n
  | fuel + 1, a, k, n =>
    if k = 0 then 1 % n
    else if k % 2 = 1 then powModAux fuel (a * a % n) (k / 2) n * a % n
    else powModAux fuel (a * a % n) (k / 2) n

/- Correctness of powModAux.  k < 2^fuel ⇒ powModAux fuel a k n = a^k % n -/
theorem powModAux_eq : ∀ (fuel a k n : ℕ), k < 2 ^ fuel → powModAux fuel a k n = a ^ k % n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a k n hk
    rw [pow_zero] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [powModAux]
  | succ f ih =>
    intro a k n hk
    by_cases hk0 : k = 0
    · subst hk0; simp [powModAux]
    · have hk2 : k / 2 < 2 ^ f := by
        rw [pow_succ] at hk
        omega
      have hrec := ih (a * a % n) (k / 2) n hk2
      have haa : a * a = a ^ 2 := (pow_two a).symm
      simp only [powModAux, if_neg hk0]
      by_cases hodd : k % 2 = 1
      · rw [if_pos hodd, hrec, ← Nat.pow_mod, Nat.mod_mul_mod, haa, ← pow_mul, ← pow_succ,
          show 2 * (k / 2) + 1 = k by omega]
      · rw [if_neg hodd, hrec, ← Nat.pow_mod, haa, ← pow_mul,
          show 2 * (k / 2) = k by omega]

/-- powMod a k n = a^k % n for all k < 2^256.  Fuel fixed at 256 — enough for
    all exponents in the certificate (n ≤ p < 2^255). -/
def powMod (a k n : ℕ) : ℕ := powModAux 256 a k n

theorem cast_pow_eq (a k n : ℕ) (hk : k < 2 ^ 256) :
    (a : ZMod n) ^ k = ((powMod a k n : ℕ) : ZMod n) := by
  rw [powMod, powModAux_eq 256 a k n hk, ZMod.natCast_mod, Nat.cast_pow]

theorem pow_eq_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (h : powMod a k n = 1) :
    (a : ZMod n) ^ k = 1 := by
  rw [cast_pow_eq a k n hk, h, Nat.cast_one]

theorem pow_ne_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (hn : 1 < n)
    (h1 : powMod a k n ≠ 1) (h2 : powMod a k n < n) :
    (a : ZMod n) ^ k ≠ 1 := by
  rw [cast_pow_eq a k n hk]
  intro hcon
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by rw [Nat.cast_one],
      ZMod.natCast_eq_natCast_iff'] at hcon
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hn] at hcon
  exact h1 hcon

-- ═════════════════════════════════════════════════════════════════════════════
-- The certificate chain (leaves first, building up to the root)
-- ═════════════════════════════════════════════════════════════════════════════

/-- Leaf: 14923 is prime.  Witness g = 2.  14923−1 = 2 · 3² · 829 -/
theorem prime_14923 : Nat.Prime 14923 := by
  refine lucas_primality 14923 ((2 : ℕ) : ZMod 14923) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (14923 - 1) 14923 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (14923 : ℕ) - 1 = 2 * (3 ^ 2 * (829)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((14923 - 1) / 2) 14923 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((14923 - 1) / 3) 14923 (by decide) (by decide) (by decide) (by decide)
    have he : q = 829 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((14923 - 1) / 829) 14923 (by decide) (by decide) (by decide) (by decide)

/-- Leaf: 115603 is prime.  Witness g = 2.  115603−1 = 2 · 3 · 19267 -/
theorem prime_115603 : Nat.Prime 115603 := by
  refine lucas_primality 115603 ((2 : ℕ) : ZMod 115603) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (115603 - 1) 115603 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (115603 : ℕ) - 1 = 2 * (3 * (19267)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((115603 - 1) / 2) 115603 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((115603 - 1) / 3) 115603 (by decide) (by decide) (by decide) (by decide)
    have he : q = 19267 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((115603 - 1) / 19267) 115603 (by decide) (by decide) (by decide) (by decide)

/-- Leaf: 1197907 is prime.  Witness g = 3.  1197907−1 = 2 · 3 · 53 · 3767 -/
theorem prime_1197907 : Nat.Prime 1197907 := by
  refine lucas_primality 1197907 ((3 : ℕ) : ZMod 1197907) ?_ ?_
  · exact pow_eq_one_of_powMod 3 (1197907 - 1) 1197907 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (1197907 : ℕ) - 1 = 2 * (3 * (53 * (3767))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((1197907 - 1) / 2) 1197907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((1197907 - 1) / 3) 1197907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 53 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((1197907 - 1) / 53) 1197907 (by decide) (by decide) (by decide) (by decide)
    have he : q = 3767 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 3 ((1197907 - 1) / 3767) 1197907 (by decide) (by decide) (by decide) (by decide)

/-- Leaf: 463 is prime.  Witness g = 3.  463−1 = 2 · 3 · 7 · 11 -/
theorem prime_463 : Nat.Prime 463 := by
  refine lucas_primality 463 ((3 : ℕ) : ZMod 463) ?_ ?_
  · exact pow_eq_one_of_powMod 3 (463 - 1) 463 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (463 : ℕ) - 1 = 2 * (3 * (7 * (11))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((463 - 1) / 2) 463 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((463 - 1) / 3) 463 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((463 - 1) / 7) 463 (by decide) (by decide) (by decide) (by decide)
    have he : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 3 ((463 - 1) / 11) 463 (by decide) (by decide) (by decide) (by decide)

/-- Leaf: 2531 is prime.  Witness g = 2.  2531−1 = 2 · 5 · 11 · 23 -/
theorem prime_2531 : Nat.Prime 2531 := by
  refine lucas_primality 2531 ((2 : ℕ) : ZMod 2531) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (2531 - 1) 2531 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (2531 : ℕ) - 1 = 2 * (5 * (11 * (23))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((2531 - 1) / 2) 2531 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((2531 - 1) / 5) 2531 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((2531 - 1) / 11) 2531 (by decide) (by decide) (by decide) (by decide)
    have he : q = 23 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((2531 - 1) / 23) 2531 (by decide) (by decide) (by decide) (by decide)

/-- Node: 417677162933 is prime.  Witness g = 2.
    417677162933−1 = 2² · 59 · 1973 · 897019 -/
theorem prime_417677162933 : Nat.Prime 417677162933 := by
  refine lucas_primality 417677162933 ((2 : ℕ) : ZMod 417677162933) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (417677162933 - 1) 417677162933 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (417677162933 : ℕ) - 1 = 2 ^ 2 * (59 * (1973 * (897019))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((417677162933 - 1) / 2) 417677162933 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 59 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((417677162933 - 1) / 59) 417677162933 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 1973 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((417677162933 - 1) / 1973) 417677162933 (by decide) (by decide) (by decide) (by decide)
    have he : q = 897019 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((417677162933 - 1) / 897019) 417677162933 (by decide) (by decide) (by decide) (by decide)

/-- Node: 22160661629 is prime.  Witness g = 3.
    22160661629−1 = 2² · 7 · 19 · 41655379 -/
theorem prime_22160661629 : Nat.Prime 22160661629 := by
  refine lucas_primality 22160661629 ((3 : ℕ) : ZMod 22160661629) ?_ ?_
  · exact pow_eq_one_of_powMod 3 (22160661629 - 1) 22160661629 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (22160661629 : ℕ) - 1 = 2 ^ 2 * (7 * (19 * (41655379))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 3 ((22160661629 - 1) / 2) 22160661629 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((22160661629 - 1) / 7) 22160661629 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 3 ((22160661629 - 1) / 19) 22160661629 (by decide) (by decide) (by decide) (by decide)
    have he : q = 41655379 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 3 ((22160661629 - 1) / 41655379) 22160661629 (by decide) (by decide) (by decide) (by decide)

/-- Node: 325086459374267 is prime.  Witness g = 2.
    325086459374267−1 = 2 · 509 · 413527 · 772231 -/
theorem prime_325086459374267 : Nat.Prime 325086459374267 := by
  refine lucas_primality 325086459374267 ((2 : ℕ) : ZMod 325086459374267) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (325086459374267 - 1) 325086459374267 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (325086459374267 : ℕ) - 1 = 2 * (509 * (413527 * (772231))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((325086459374267 - 1) / 2) 325086459374267 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 509 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((325086459374267 - 1) / 509) 325086459374267 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 413527 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((325086459374267 - 1) / 413527) 325086459374267 (by decide) (by decide) (by decide) (by decide)
    have he : q = 772231 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((325086459374267 - 1) / 772231) 325086459374267 (by decide) (by decide) (by decide) (by decide)

/-- Node f1 = 539204044132271846773 (69 bits).  Witness g = 5.
    f1−1 = 2² · 3⁵ · 89 · 14923 · 417677162933
    Recursive: 14923 and 417677162933 certified above. -/
theorem prime_539204044132271846773 : Nat.Prime 539204044132271846773 := by
  refine lucas_primality 539204044132271846773 ((5 : ℕ) : ZMod 539204044132271846773) ?_ ?_
  · exact pow_eq_one_of_powMod 5 (539204044132271846773 - 1) 539204044132271846773 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (539204044132271846773 : ℕ) - 1 = 2 ^ 2 * (3 ^ 5 * (89 * (14923 * (417677162933)))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 5 ((539204044132271846773 - 1) / 2) 539204044132271846773 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 5 ((539204044132271846773 - 1) / 3) 539204044132271846773 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 89 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((539204044132271846773 - 1) / 89) 539204044132271846773 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 14923 := (Nat.prime_dvd_prime_iff_eq hq prime_14923).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((539204044132271846773 - 1) / 14923) 539204044132271846773 (by decide) (by decide) (by decide) (by decide)
    have he : q = 417677162933 := (Nat.prime_dvd_prime_iff_eq hq prime_417677162933).mp hqd
    subst he
    exact pow_ne_one_of_powMod 5 ((539204044132271846773 - 1) / 417677162933) 539204044132271846773 (by decide) (by decide) (by decide) (by decide)

/-- Node f2 = 8999194758858563409123804352480028797519453 (143 bits).  Witness g = 2.
    f2−1 = 2² · 3⁴ · 11 · 2531 · 115603 · 1197907 · 22160661629 · 325086459374267
    Recursive: large factors certified above. -/
theorem prime_8999194758858563409123804352480028797519453 : Nat.Prime 8999194758858563409123804352480028797519453 := by
  refine lucas_primality 8999194758858563409123804352480028797519453 ((2 : ℕ) : ZMod 8999194758858563409123804352480028797519453) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (8999194758858563409123804352480028797519453 - 1) 8999194758858563409123804352480028797519453 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (8999194758858563409123804352480028797519453 : ℕ) - 1 =
        2 ^ 2 * (3 ^ 4 * (11 * (2531 * (115603 * (1197907 * (22160661629 * (325086459374267))))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 2) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 3) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 11 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 11) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2531 := (Nat.prime_dvd_prime_iff_eq hq prime_2531).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 2531) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 115603 := (Nat.prime_dvd_prime_iff_eq hq prime_115603).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 115603) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 1197907 := (Nat.prime_dvd_prime_iff_eq hq prime_1197907).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 1197907) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 22160661629 := (Nat.prime_dvd_prime_iff_eq hq prime_22160661629).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 22160661629) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)
    have he : q = 325086459374267 := (Nat.prime_dvd_prime_iff_eq hq prime_325086459374267).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((8999194758858563409123804352480028797519453 - 1) / 325086459374267) 8999194758858563409123804352480028797519453 (by decide) (by decide) (by decide) (by decide)

/-- ROOT: Pallas base-field modulus P is prime.  Witness g = 5.
    P−1 = 2³² · 3 · 463 · f1 · f2
    with f1, f2 certified recursively above. -/
theorem prime_Pallas : Nat.Prime 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
  refine lucas_primality 28948022309329048855892746252171976963363056481941560715954676764349967630337
    ((5 : ℕ) : ZMod 28948022309329048855892746252171976963363056481941560715954676764349967630337) ?_ ?_
  · exact pow_eq_one_of_powMod 5
      (28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1)
      28948022309329048855892746252171976963363056481941560715954676764349967630337
      (by decide) (by decide)
  · intro q hq hqd
    have hfac : (28948022309329048855892746252171976963363056481941560715954676764349967630337 : ℕ) - 1 =
        2 ^ 32 * (3 * (463 * (539204044132271846773 * (8999194758858563409123804352480028797519453)))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 5
        ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 2)
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5
        ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 3)
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 463 := (Nat.prime_dvd_prime_iff_eq hq prime_463).mp h
      subst he
      exact pow_ne_one_of_powMod 5
        ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 463)
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 539204044132271846773 := (Nat.prime_dvd_prime_iff_eq hq prime_539204044132271846773).mp h
      subst he
      exact pow_ne_one_of_powMod 5
        ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 539204044132271846773)
        28948022309329048855892746252171976963363056481941560715954676764349967630337
        (by decide) (by decide) (by decide) (by decide)
    have he : q = 8999194758858563409123804352480028797519453 :=
      (Nat.prime_dvd_prime_iff_eq hq prime_8999194758858563409123804352480028797519453).mp hqd
    subst he
    exact pow_ne_one_of_powMod 5
      ((28948022309329048855892746252171976963363056481941560715954676764349967630337 - 1) / 8999194758858563409123804352480028797519453)
      28948022309329048855892746252171976963363056481941560715954676764349967630337
      (by decide) (by decide) (by decide) (by decide)

end PPallas

-- ═════════════════════════════════════════════════════════════════════════════
-- Exported result
-- ═════════════════════════════════════════════════════════════════════════════

/-- The Pallas curve base field modulus is prime.
    This is the only theorem from this file used downstream. -/
theorem pallas_prime : Nat.Prime 28948022309329048855892746252171976963363056481941560715954676764349967630337 :=
  PPallas.prime_Pallas
