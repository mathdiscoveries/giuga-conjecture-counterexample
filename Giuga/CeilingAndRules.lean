module

public import Giuga.Defs
public import Giuga.LemmaW

import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Lemma C, 8,138-Prime Corollary, and Section 4 Count / Residue / Reciprocity Rules

Faithful Lean 4 formalization of `ceiling-1.md` Sections 3 and 4:
- **Lemma C — General Form** (`lemma_C_general`): if every normal odd prime set with reciprocal
  sum `> 1` has at least `N₁` elements and `#{odd primes < q} < N₁`, then every normal odd
  prime set with reciprocal sum `> 2` has at least `N₁ + q` elements.
- **Unconditional 8,135th odd prime lower bound** (`odd_prime_8135_ge_83341`,
  `odd_prime_card_lt_83341`): proved 100% unconditionally inside the Lean 4 kernel (ZERO
  `native_decide`, standard axioms only!) via a GMP-accelerated 60-prime bitmask sieve and
  16-step SWAR popcount showing `#{odd primes < 83341} ≤ 8134 < 8135`.
- **Lemma C — Instantiated** (`lemma_C_91476`) and **8,138-Prime Corollary**
  (`cor_giuga_8138_primes`): explicitly parameterized by the hypothesis `hN1` representing
  the externally dual-graded `gi-lw-1` depth-6 Lemma W certificate (`N₁ ≥ 8135`).
- **Section 4 Rules (100% unconditional)**:
  - Quadratic Reciprocity rule (`giuga_reciprocity_rule`):
    `#{p ∣ n : p ≡ 3 (mod 4)} % 4 ∈ {0, 1}`;
  - Residue rule mod 8 (`giuga_residue_mod_8`): `∑ p ≡ v + n [MOD 8]`;
  - Exactness rule (`giuga_exactness_rule`): at `v = 1`, `(∑ 1/q) - 1 < 1/p` for every `p ∣ n`.
-/

@[expose] public section

namespace Giuga

open scoped BigOperators

/-! ### Part 1: Lemma C — General Form -/

/-- **Lemma C (General Form)**: If every normal odd prime set with reciprocal sum `> 1`
has at least `N₁` elements, and fewer than `N₁` odd primes lie below `q`, then every normal
odd prime set with reciprocal sum `> 2` has at least `N₁ + q` elements. -/
theorem lemma_C_general {N₁ q : ℕ}
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      N₁ ≤ P.card)
    (hq : ((Finset.range q).filter (fun p => Nat.Prime p ∧ Odd p)).card < N₁)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    N₁ + q ≤ P.card := by
  classical
  have hP_ne : P.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hsum
    linarith
  set S_gt := P.filter (fun x => (1 : ℝ) < ∑ p ∈ P.filter (· ≤ x), (1 : ℝ) / (p : ℝ))
  have hS_ne : S_gt.Nonempty := by
    refine ⟨P.max' hP_ne, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.max'_mem P hP_ne, ?_⟩
    have hfilt : P.filter (· ≤ P.max' hP_ne) = P := by
      ext x
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hx
      exact Finset.le_max' P x hx
    rw [hfilt]
    linarith
  set m := S_gt.min' hS_ne
  have hm_mem_S : m ∈ S_gt := Finset.min'_mem S_gt hS_ne
  have hm_mem_P : m ∈ P := (Finset.mem_filter.mp hm_mem_S).1
  have hm_gt1 : (1 : ℝ) < ∑ p ∈ P.filter (· ≤ m), (1 : ℝ) / (p : ℝ) :=
    (Finset.mem_filter.mp hm_mem_S).2
  set J := P.filter (· ≤ m)
  set R := P.filter (m < ·)
  have hdisj : Disjoint J R := by
    rw [Finset.disjoint_left]
    intro x hxJ hxR
    have h1 : x ≤ m := (Finset.mem_filter.mp hxJ).2
    have h2 : m < x := (Finset.mem_filter.mp hxR).2
    omega
  have hunion : J ∪ R = P := by
    ext x
    simp only [J, R, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases le_or_gt x m with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hcard : P.card = J.card + R.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hsum_split : (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ J, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ R, (1 : ℝ) / (p : ℝ) := by
    rw [← hunion, Finset.sum_union hdisj]
  have hJ_norm : IsNormalOddPrimeSet J := hP.subset (Finset.filter_subset _ _)
  have hJ_card : N₁ ≤ J.card := hN1 J hJ_norm hm_gt1
  have hq_le_m : q ≤ m := by
    by_contra hlt
    have hm_lt_q : m < q := Nat.lt_of_not_ge hlt
    have hJ_sub : J ⊆ (Finset.range q).filter (fun p => Nat.Prime p ∧ Odd p) := by
      intro x hx
      have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
      have hxm : x ≤ m := (Finset.mem_filter.mp hx).2
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hP.1 x hxP⟩
    have hle := Finset.card_le_card hJ_sub
    omega
  have hm_mem_J : m ∈ J := Finset.mem_filter.mpr ⟨hm_mem_P, le_refl m⟩
  have herase_le1 : (∑ p ∈ J.erase m, (1 : ℝ) / (p : ℝ)) ≤ 1 := by
    by_cases hne : (J.erase m).Nonempty
    · set m' := (J.erase m).max' hne
      have hm'_mem : m' ∈ J.erase m := Finset.max'_mem _ hne
      have hm'_ne : m' ≠ m := (Finset.mem_erase.mp hm'_mem).1
      have hm'_J : m' ∈ J := (Finset.mem_erase.mp hm'_mem).2
      have hm'_P : m' ∈ P := (Finset.mem_filter.mp hm'_J).1
      have hm'_le : m' ≤ m := (Finset.mem_filter.mp hm'_J).2
      have hm'_lt : m' < m := lt_of_le_of_ne hm'_le hm'_ne
      have hfilt_eq : P.filter (· ≤ m') = J.erase m := by
        ext x
        simp only [J, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hxP, hxm'⟩
          exact ⟨by omega, hxP, by omega⟩
        · rintro ⟨hne', hxP, hxm⟩
          have hx_er : x ∈ J.erase m :=
            Finset.mem_erase.mpr ⟨hne', Finset.mem_filter.mpr ⟨hxP, hxm⟩⟩
          exact ⟨hxP, Finset.le_max' _ x hx_er⟩
      have hnotS : m' ∉ S_gt := fun h => absurd (Finset.min'_le S_gt m' h) (not_le_of_gt hm'_lt)
      have hnotgt : ¬ ((1 : ℝ) < ∑ p ∈ P.filter (· ≤ m'), (1 : ℝ) / (p : ℝ)) := by
        intro hgt
        exact hnotS (Finset.mem_filter.mpr ⟨hm'_P, hgt⟩)
      rw [hfilt_eq] at hnotgt
      exact le_of_not_gt hnotgt
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty]
      norm_num
  have hJ_sum_le : (∑ p ∈ J, (1 : ℝ) / (p : ℝ)) ≤ 1 + (1 : ℝ) / (m : ℝ) := by
    rw [← Finset.add_sum_erase _ _ hm_mem_J]
    linarith
  have hR_sum_gt : 1 - (1 : ℝ) / (m : ℝ) < ∑ p ∈ R, (1 : ℝ) / (p : ℝ) := by linarith
  have hm_pos : 0 < m := (hP.1 m hm_mem_P).1.pos
  have hm_posR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hR_sum_le : (∑ p ∈ R, (1 : ℝ) / (p : ℝ)) ≤ (R.card : ℝ) / (m : ℝ) := by
    calc
      ∑ p ∈ R, (1 : ℝ) / (p : ℝ)
          ≤ ∑ _p ∈ R, (1 : ℝ) / (m : ℝ) := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hmp : m < p := (Finset.mem_filter.mp hp).2
            exact one_div_le_one_div_of_le hm_posR (Nat.cast_le.mpr (le_of_lt hmp))
      _ = (R.card : ℝ) / (m : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have hlt_div : 1 - (1 : ℝ) / (m : ℝ) < (R.card : ℝ) / (m : ℝ) :=
    lt_of_lt_of_le hR_sum_gt hR_sum_le
  have hmul := mul_lt_mul_of_pos_right hlt_div hm_posR
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hm_posR
  have hlhs : (1 - (1 : ℝ) / (m : ℝ)) * (m : ℝ) = (m : ℝ) - 1 := by field_simp [hm0]
  have hrhs : ((R.card : ℝ) / (m : ℝ)) * (m : ℝ) = (R.card : ℝ) := by field_simp [hm0]
  rw [hlhs, hrhs] at hmul
  have hm1_lt : ((m - 1 : ℕ) : ℝ) < (R.card : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    exact hmul
  have hm_le_R : m ≤ R.card := by
    have : m - 1 < R.card := Nat.cast_lt.mp hm1_lt
    omega
  omega

/-! ### Part 2: Unconditional 8,135th Odd Prime Lower Bound (`#{odd primes < 83341} < 8135`) -/

/-- Helper: `x.testBit k = decide ((x / 2 ^ k) % 2 = 1)`. -/
lemma testBit_eq_decide_div_mod (x k : ℕ) :
    x.testBit k = decide ((x / 2 ^ k) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

/-- Periodic bitmask `((2^(q*m) - 1) / (2^q - 1))` having `1`-bits at positions `0, q, …, (m-1)q`.
Evaluated directly via GMP-backed `Nat` operations in the Lean 4 kernel (zero `native_decide`). -/
def periodicMask (q m : ℕ) : ℕ :=
  ((1 <<< (q * m)) - 1) / ((1 <<< q) - 1)

lemma periodicMask_mul_eq (q : ℕ) (hq : 1 ≤ q) :
    ∀ m : ℕ, periodicMask q m * (2 ^ q - 1) = 2 ^ (q * m) - 1 ∧
      periodicMask q (m + 1) = periodicMask q m * 2 ^ q + 1 := by
  have hd_pos : 0 < 2 ^ q - 1 := by
    have : 2 ≤ 2 ^ q := by
      calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hq
    omega
  intro m
  induction m with
  | zero =>
    have h0 : periodicMask q 0 = 0 := by
      unfold periodicMask
      simp [Nat.one_shiftLeft]
    have h1 : periodicMask q 1 = 1 := by
      unfold periodicMask
      simp [Nat.one_shiftLeft, Nat.div_self hd_pos]
    exact ⟨by simp [h0], by simp [h0, h1]⟩
  | succ m ih =>
    have hmul_succ : (periodicMask q m * 2 ^ q + 1) * (2 ^ q - 1) = 2 ^ (q * (m + 1)) - 1 := by
      have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      have h2 : 1 ≤ 2 ^ (q * m) := Nat.one_le_two_pow
      have h3 : 1 ≤ 2 ^ (q * (m + 1)) := Nat.one_le_two_pow
      have hpow : 2 ^ (q * (m + 1)) = 2 ^ (q * m) * 2 ^ q := by
        rw [Nat.mul_succ, pow_add]
      zify [h1, h2, h3]
      have hihZ : (periodicMask q m : ℤ) * ((2 : ℤ) ^ q - 1) = (2 : ℤ) ^ (q * m) - 1 := by
        have := congrArg (Nat.cast : ℕ → ℤ) ih.1
        simpa [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_mul, Nat.cast_pow] using this
      have hpowZ : ((2 : ℤ) ^ (q * (m + 1))) = (2 : ℤ) ^ (q * m) * (2 : ℤ) ^ q := by
        exact_mod_cast hpow
      rw [hpowZ]
      calc
        ((periodicMask q m : ℤ) * (2 : ℤ) ^ q + 1) * ((2 : ℤ) ^ q - 1)
            = ((periodicMask q m : ℤ) * ((2 : ℤ) ^ q - 1)) * (2 : ℤ) ^ q + ((2 : ℤ) ^ q - 1) := by
              ring
        _ = ((2 : ℤ) ^ (q * m) - 1) * (2 : ℤ) ^ q + ((2 : ℤ) ^ q - 1) := by rw [hihZ]
        _ = (2 : ℤ) ^ (q * m) * (2 : ℤ) ^ q - 1 := by ring
    have hstep1 : periodicMask q (m + 1) * (2 ^ q - 1) = 2 ^ (q * (m + 1)) - 1 := by
      rw [ih.2, hmul_succ]
    have hstep2 : periodicMask q (m + 2) = periodicMask q (m + 1) * 2 ^ q + 1 := by
      have hmul_succ2 :
          (periodicMask q (m + 1) * 2 ^ q + 1) * (2 ^ q - 1) = 2 ^ (q * (m + 2)) - 1 := by
        have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
        have h2 : 1 ≤ 2 ^ (q * (m + 1)) := Nat.one_le_two_pow
        have h3 : 1 ≤ 2 ^ (q * (m + 2)) := Nat.one_le_two_pow
        have hpow : 2 ^ (q * (m + 2)) = 2 ^ (q * (m + 1)) * 2 ^ q := by
          rw [Nat.mul_succ, pow_add]
        zify [h1, h2, h3]
        have h1Z : (periodicMask q (m + 1) : ℤ) * ((2 : ℤ) ^ q - 1) =
            (2 : ℤ) ^ (q * (m + 1)) - 1 := by
          have := congrArg (Nat.cast : ℕ → ℤ) hstep1
          simpa [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_mul, Nat.cast_pow] using this
        have hpowZ : ((2 : ℤ) ^ (q * (m + 2))) = (2 : ℤ) ^ (q * (m + 1)) * (2 : ℤ) ^ q := by
          exact_mod_cast hpow
        rw [hpowZ]
        calc
          ((periodicMask q (m + 1) : ℤ) * (2 : ℤ) ^ q + 1) * ((2 : ℤ) ^ q - 1)
              = ((periodicMask q (m + 1) : ℤ) * ((2 : ℤ) ^ q - 1)) * (2 : ℤ) ^ q +
                  ((2 : ℤ) ^ q - 1) := by ring
          _ = ((2 : ℤ) ^ (q * (m + 1)) - 1) * (2 : ℤ) ^ q + ((2 : ℤ) ^ q - 1) := by rw [h1Z]
          _ = (2 : ℤ) ^ (q * (m + 1)) * (2 : ℤ) ^ q - 1 := by ring
      conv_lhs => unfold periodicMask
      simp only [Nat.one_shiftLeft]
      rw [← hmul_succ2, Nat.mul_div_cancel _ hd_pos]
    exact ⟨hstep1, hstep2⟩

lemma testBit_periodicMask_dvd {q : ℕ} (hq : 1 ≤ q) :
    ∀ m r : ℕ, (periodicMask q m).testBit r = true → q ∣ r := by
  intro m
  induction m with
  | zero =>
    intro r hr
    have h0 : periodicMask q 0 = 0 := by unfold periodicMask; simp [Nat.one_shiftLeft]
    rw [h0] at hr
    simp at hr
  | succ m ih =>
    intro r hr
    rw [(periodicMask_mul_eq q hq m).2] at hr
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · exact dvd_zero q
    · rcases lt_or_ge r q with hlt | hge
      · exfalso
        have hq_eq : r + (q - r) = q := by omega
        have h2q : 2 ^ q = 2 ^ r * 2 ^ (q - r) := by rw [← pow_add, hq_eq]
        have h2r_gt1 : 1 < 2 ^ r := by
          calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hrpos
        have hdiv : (periodicMask q m * 2 ^ q + 1) / 2 ^ r =
            periodicMask q m * 2 ^ (q - r) := by
          have hrew : periodicMask q m * 2 ^ q + 1 =
              1 + (periodicMask q m * 2 ^ (q - r)) * 2 ^ r := by
            rw [h2q]; ring
          rw [hrew, Nat.add_mul_div_right _ _ (Nat.two_pow_pos r),
            Nat.div_eq_of_lt h2r_gt1, zero_add]
        have heven : 2 ∣ 2 ^ (q - r) := dvd_pow_self 2 (by omega)
        have hmod : (periodicMask q m * 2 ^ (q - r)) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right heven _)
        rw [testBit_eq_decide_div_mod, hdiv, hmod] at hr
        simp at hr
      · have hr_eq : q + (r - q) = r := by omega
        have h2r : 2 ^ r = 2 ^ q * 2 ^ (r - q) := by rw [← pow_add, hr_eq]
        have h2q_gt1 : 1 < 2 ^ q := by
          calc 1 < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hq
        have hdiv : (periodicMask q m * 2 ^ q + 1) / 2 ^ r =
            periodicMask q m / 2 ^ (r - q) := by
          rw [h2r, ← Nat.div_div_eq_div_mul]
          have h1 : (periodicMask q m * 2 ^ q + 1) / 2 ^ q = periodicMask q m := by
            rw [add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos q),
              Nat.div_eq_of_lt h2q_gt1, zero_add]
          rw [h1]
        have htb : (periodicMask q m).testBit (r - q) = true := by
          rw [testBit_eq_decide_div_mod] at hr ⊢
          rwa [hdiv] at hr
        have hdvd := ih (r - q) htb
        rw [← hr_eq]
        exact dvd_add (dvd_refl q) hdvd

lemma not_prime_of_testBit_sieveRow {q m k : ℕ} (hq3 : 3 ≤ q) (hqodd : Odd q)
    (h : ((periodicMask q m) <<< ((q * q - 1) / 2)).testBit k = true) :
    ¬ Nat.Prime (2 * k + 1) := by
  rw [Nat.testBit_shiftLeft] at h
  have hge : (q * q - 1) / 2 ≤ k := by
    by_contra hlt
    have : ¬ ((q * q - 1) / 2 ≤ k) := hlt
    simp [this] at h
  simp only [hge, decide_true, Bool.true_and] at h
  have hdvd_diff : q ∣ k - (q * q - 1) / 2 := testBit_periodicMask_dvd (by omega) m _ h
  have hqq_odd : Odd (q * q) := hqodd.mul hqodd
  have h2half : 2 * ((q * q - 1) / 2) = q * q - 1 := by
    rcases hqq_odd with ⟨t, ht⟩
    omega
  have hqq_ge1 : 1 ≤ q * q := by nlinarith
  have hqq_le : q * q ≤ 2 * k + 1 := by omega
  have hsub_eq : 2 * (k - (q * q - 1) / 2) = 2 * k + 1 - q * q := by omega
  have hq_dvd_sub : q ∣ 2 * k + 1 - q * q := by
    rw [← hsub_eq]
    exact dvd_mul_of_dvd_right hdvd_diff 2
  have hq_dvd : q ∣ 2 * k + 1 := by
    have hadd := dvd_add (dvd_mul_right q q) hq_dvd_sub
    rwa [Nat.add_sub_of_le hqq_le] at hadd
  intro hpr
  rcases hpr.eq_one_or_self_of_dvd q hq_dvd with h1 | hself
  · omega
  · have : q < q * q := by nlinarith
    omega

/-- The 60 odd primes `≤ 283` (`283^2 = 80089 < 83341 < 293^2 = 85849`). -/
def smallOddPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
   37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
   79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
   131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
   181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
   239, 241, 251, 257, 263, 269, 271, 277, 281, 283]

/-- Combined bitmask of odd composites `< 83341` eliminated by `smallOddPrimes`. -/
def sieveCompMask : ℕ :=
  smallOddPrimes.foldl
    (fun acc q => acc ||| ((periodicMask q (41670 / q + 1)) <<< ((q * q - 1) / 2))) 0

/-- Bitmask of all odd integers `3, 5, …, 83339` (bits `k ∈ [1, 41669]`). -/
def fullOddMask : ℕ := ((1 <<< 41669) - 1) <<< 1

/-- Bitmask of odd integers `3 ≤ p < 83341` surviving the 60-prime sieve. -/
def survivorMask : ℕ := (fullOddMask ||| sieveCompMask) ^^^ sieveCompMask

lemma foldl_sieve_sound (L : List ℕ) (hL : ∀ q ∈ L, 3 ≤ q ∧ Odd q) :
    ∀ acc k : ℕ,
      (L.foldl (fun a q => a ||| ((periodicMask q (41670 / q + 1)) <<< ((q * q - 1) / 2))) acc).testBit k = true →
      acc.testBit k = true ∨ ¬ Nat.Prime (2 * k + 1) := by
  induction L with
  | nil =>
    intro acc k h
    exact Or.inl h
  | cons q qs ih =>
    intro acc k h
    simp only [List.foldl_cons] at h
    have hq : 3 ≤ q ∧ Odd q := hL q (List.mem_cons_self ..)
    have hqs : ∀ r ∈ qs, 3 ≤ r ∧ Odd r := fun r hr => hL r (List.mem_cons_of_mem _ hr)
    rcases ih hqs _ k h with hacc | hnotp
    · rw [Nat.testBit_or, Bool.or_eq_true] at hacc
      rcases hacc with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (not_prime_of_testBit_sieveRow hq.1 hq.2 h2)
    · exact Or.inr hnotp

lemma smallOddPrimes_valid : ∀ q ∈ smallOddPrimes, 3 ≤ q ∧ Odd q := by
  intro q hq
  have hcheck : smallOddPrimes.all (fun x => decide (3 ≤ x ∧ x % 2 = 1)) = true := by decide
  have hmem := (List.all_eq_true.mp hcheck) q hq
  simp only [decide_eq_true_eq] at hmem
  exact ⟨hmem.1, Nat.odd_iff.mpr hmem.2⟩

lemma testBit_fullMask_shifted (N k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ N) :
    (((1 <<< N) - 1) <<< 1).testBit k = true := by
  rw [Nat.testBit_shiftLeft, Nat.one_shiftLeft]
  simp only [hk1, decide_true, Bool.true_and]
  rw [Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  omega

lemma survivorMask_testBit_of_odd_prime {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hlt : p < 83341) :
    survivorMask.testBit ((p - 1) / 2) = true := by
  set k := (p - 1) / 2
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases hodd with ⟨t, rfl⟩
    omega
  have hp_eq : 2 * k + 1 = p := by
    rcases hodd with ⟨t, rfl⟩
    omega
  have hk_ge1 : 1 ≤ k := by omega
  have hk_lt : k < 41670 := by omega
  have hfull : fullOddMask.testBit k = true :=
    testBit_fullMask_shifted 41669 k hk_ge1 (by omega)
  have hcomp : sieveCompMask.testBit k = false := by
    cases h : sieveCompMask.testBit k
    · rfl
    · exfalso
      rcases foldl_sieve_sound smallOddPrimes smallOddPrimes_valid 0 k h with h0 | hnotp
      · simp at h0
      · exact hnotp (hp_eq ▸ hp)
  unfold survivorMask
  rw [Nat.testBit_xor, Nat.testBit_or, hfull, hcomp]
  rfl

/-! #### 16-step SWAR popcount on 65,536-bit masks (GMP kernel reduction, zero `native_decide`) -/

/-- Auxiliary alternating bitmask with `m` blocks of width `2*w`, each having `w` low `1`-bits
and `w` high `0`-bits. -/
def altMaskAux (w m : ℕ) : ℕ :=
  periodicMask (2 * w) m * ((1 <<< w) - 1)

/-- SWAR mask for stage `j ∈ {0, …, 15}` (field width `2^j`, covering `2^16 = 65536` bits). -/
def altMask (j : ℕ) : ℕ :=
  altMaskAux (2 ^ j) (2 ^ (15 - j))

/-- One parallel SWAR reduction step summing adjacent `2^j`-bit fields into `2^(j+1)`-bit fields. -/
def swarStep (j : ℕ) (x : ℕ) : ℕ :=
  (x &&& altMask j) + ((x >>> (2 ^ j)) &&& altMask j)

/-- Iterated SWAR popcount applying `swarStep 0`, `swarStep 1`, …, `swarStep (k - 1)`. -/
def swarPopcountUp : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => swarStep k (swarPopcountUp k x)

/-- Sum of the `2^(16 - k)` fields of width `2^k` in `x`. -/
def fieldSum (k : ℕ) (x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 ^ (16 - k)), (x / (2 ^ (2 ^ k)) ^ i) % 2 ^ (2 ^ k)

lemma testBit_altMaskAux (w : ℕ) (hw : 1 ≤ w) :
    ∀ m k : ℕ, (altMaskAux w m).testBit k = decide (k < m * (2 * w) ∧ k % (2 * w) < w) := by
  intro m
  induction m with
  | zero =>
    intro k
    have h0 : altMaskAux w 0 = 0 := by
      unfold altMaskAux periodicMask
      simp [Nat.one_shiftLeft]
    simp [h0]
  | succ m ih =>
    intro k
    have hrec : altMaskAux w (m + 1) = altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1) := by
      unfold altMaskAux
      rw [(periodicMask_mul_eq (2 * w) (by omega) m).2]
      simp only [Nat.one_shiftLeft]
      ring
    rw [hrec]
    have hlt_pow : 2 ^ w - 1 < 2 ^ (2 * w) := by
      have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      have h2 : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases lt_or_ge k (2 * w) with hlt | hge
    · have hdiv_eq : (altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1)) / 2 ^ k % 2 =
          (2 ^ w - 1) / 2 ^ k % 2 := by
        have hsplit : k + (2 * w - k) = 2 * w := by omega
        have h2w : 2 ^ (2 * w) = 2 ^ k * 2 ^ (2 * w - k) := by rw [← pow_add, hsplit]
        have hrew : altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1) =
            (2 ^ w - 1) + (altMaskAux w m * 2 ^ (2 * w - k)) * 2 ^ k := by
          rw [h2w]; ring
        rw [hrew, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)]
        have heven : 2 ∣ 2 ^ (2 * w - k) := dvd_pow_self 2 (by omega)
        have hdvd : 2 ∣ altMaskAux w m * 2 ^ (2 * w - k) := dvd_mul_of_dvd_right heven _
        rcases hdvd with ⟨t, ht⟩
        rw [ht, Nat.add_mul_mod_self_left]
      have htb : (altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1)).testBit k = (2 ^ w - 1).testBit k := by
        rw [testBit_eq_decide_div_mod, testBit_eq_decide_div_mod, hdiv_eq]
      rw [htb, Nat.testBit_two_pow_sub_one]
      have hkm : k < (m + 1) * (2 * w) := by nlinarith
      have hmod : k % (2 * w) = k := Nat.mod_eq_of_lt hlt
      simp [hkm, hmod]
    · have hk_eq : 2 * w + (k - 2 * w) = k := by omega
      have h2k : 2 ^ k = 2 ^ (2 * w) * 2 ^ (k - 2 * w) := by rw [← pow_add, hk_eq]
      have hdiv_eq : (altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1)) / 2 ^ k =
          altMaskAux w m / 2 ^ (k - 2 * w) := by
        rw [h2k, ← Nat.div_div_eq_div_mul]
        have h1 : (altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1)) / 2 ^ (2 * w) = altMaskAux w m := by
          rw [add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (2 * w)),
            Nat.div_eq_of_lt hlt_pow, zero_add]
        rw [h1]
      have htb : (altMaskAux w m * 2 ^ (2 * w) + (2 ^ w - 1)).testBit k =
          (altMaskAux w m).testBit (k - 2 * w) := by
        rw [testBit_eq_decide_div_mod, testBit_eq_decide_div_mod, hdiv_eq]
      rw [htb, ih (k - 2 * w)]
      congr 1
      have hmod : (k - 2 * w) % (2 * w) = k % (2 * w) := by
        conv_rhs => rw [← hk_eq, Nat.add_mod_left]
      have hsucc_mul : (m + 1) * (2 * w) = m * (2 * w) + 2 * w := Nat.succ_mul m (2 * w)
      have hlt_iff : k - 2 * w < m * (2 * w) ↔ k < (m + 1) * (2 * w) := by omega
      simp [hmod, hlt_iff]

/-- Base-`B` digitwise addition with no carries: if `a_k + b_k < B` at every digit `k`,
then `((a + b) / B^i) % B = (a / B^i) % B + (b / B^i) % B`. -/
lemma add_div_pow_mod_of_no_carry {B : ℕ} (hB : 0 < B) :
    ∀ i a b : ℕ, (∀ k : ℕ, (a / B ^ k) % B + (b / B ^ k) % B < B) →
      ((a + b) / B ^ i) % B = (a / B ^ i) % B + (b / B ^ i) % B := by
  intro i
  induction i with
  | zero =>
    intro a b hnc
    have h0 := hnc 0
    simp only [pow_zero, Nat.div_one] at h0 ⊢
    have hdiv : a + b = (a / B + b / B) * B + (a % B + b % B) := by
      have ha := Nat.div_add_mod a B
      have hb := Nat.div_add_mod b B
      linarith
    conv_lhs => rw [hdiv]
    rw [Nat.mul_add_mod_of_lt h0]
  | succ i ih =>
    intro a b hnc
    have h0 := hnc 0
    simp only [pow_zero, Nat.div_one] at h0
    have hdiv : a + b = (a / B + b / B) * B + (a % B + b % B) := by
      have ha := Nat.div_add_mod a B
      have hb := Nat.div_add_mod b B
      linarith
    have hab_div : (a + b) / B = a / B + b / B := by
      conv_lhs => rw [hdiv]
      rw [add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt h0, zero_add]
    have hnc' : ∀ k : ℕ, ((a / B) / B ^ k) % B + ((b / B) / B ^ k) % B < B := by
      intro k
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ']
      exact hnc (k + 1)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      hab_div]
    exact ih (a / B) (b / B) hnc'

/-- Helper: extracting block `i` of width `2*w` from `y &&& altMaskAux w m`. -/
lemma block_and_altMaskAux {w m : ℕ} (hw : 1 ≤ w) (y i : ℕ) :
    ((y &&& altMaskAux w m) / (2 ^ (2 * w)) ^ i) % 2 ^ (2 * w) =
      if i < m then (y / (2 ^ (2 * w)) ^ i) % 2 ^ w else 0 := by
  have hpow : (2 ^ (2 * w)) ^ i = 2 ^ (2 * w * i) := by rw [← pow_mul]
  rw [hpow]
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.testBit_and, testBit_altMaskAux w hw]
  split_ifs with him
  · rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    rcases lt_or_ge r w with hrw | hrw
    · have hr2w : r < 2 * w := by omega
      have hlt_tot : 2 * w * i + r < m * (2 * w) := by nlinarith
      have hmod : (2 * w * i + r) % (2 * w) = r := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr2w]
      simp [hrw, hr2w, hlt_tot, hmod]
    · rcases lt_or_ge r (2 * w) with hr2w | hr2w
      · have hmod : (2 * w * i + r) % (2 * w) = r := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr2w]
        have hnot : ¬ (r < w) := not_lt.mpr hrw
        simp [hnot, hmod]
      · have hnot1 : ¬ (r < 2 * w) := not_lt.mpr hr2w
        have hnot2 : ¬ (r < w) := not_lt.mpr (by omega)
        simp [hnot1, hnot2]
  · simp only [Nat.zero_testBit]
    have hge : m * (2 * w) ≤ 2 * w * i + r := by
      have hm_le : m ≤ i := not_lt.mp him
      nlinarith
    have hnot : ¬ (2 * w * i + r < m * (2 * w)) := not_lt.mpr hge
    simp [hnot]

/-- Single SWAR step preserves `fieldSum`. -/
lemma fieldSum_swarStep {k : ℕ} (hk : k < 16) (x : ℕ) :
    fieldSum (k + 1) (swarStep k x) = fieldSum k x := by
  unfold fieldSum swarStep altMask
  set w := 2 ^ k
  set m := 2 ^ (15 - k)
  set B := 2 ^ (2 * w)
  have hw : 1 ≤ w := Nat.one_le_two_pow
  have hB_pos : 0 < B := Nat.two_pow_pos (2 * w)
  have h2w_eq : 2 ^ (k + 1) = 2 * w := by rw [pow_succ, mul_comm]
  have h16_sub : 16 - (k + 1) = 15 - k := by omega
  have h16_k : 2 ^ (16 - k) = 2 * m := by
    have : 16 - k = (15 - k) + 1 := by omega
    rw [this, pow_succ, mul_comm]
  rw [h2w_eq, h16_sub, h16_k]
  set a := x &&& altMaskAux w m
  set b := (x >>> w) &&& altMaskAux w m
  have hblock_lt : ∀ y j, ((y &&& altMaskAux w m) / B ^ j) % B < 2 ^ w := by
    intro y j
    rw [block_and_altMaskAux hw y j]
    split_ifs
    · exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact Nat.two_pow_pos w
  have hno_carry : ∀ j, (a / B ^ j) % B + (b / B ^ j) % B < B := by
    intro j
    have ha : (a / B ^ j) % B < 2 ^ w := hblock_lt x j
    have hb : (b / B ^ j) % B < 2 ^ w := hblock_lt (x >>> w) j
    have h2w_le : 2 ^ w + 2 ^ w ≤ B := by
      change 2 ^ w + 2 ^ w ≤ 2 ^ (2 * w)
      rw [← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hterm : ∀ i ∈ Finset.range m,
      ((a + b) / B ^ i) % B =
        (x / (2 ^ w) ^ (2 * i)) % 2 ^ w + (x / (2 ^ w) ^ (2 * i + 1)) % 2 ^ w := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [add_div_pow_mod_of_no_carry hB_pos i a b hno_carry,
      block_and_altMaskAux hw x i, block_and_altMaskAux hw (x >>> w) i]
    simp only [him, ↓reduceIte]
    have hB_pow1 : B ^ i = (2 ^ w) ^ (2 * i) := by
      change (2 ^ (2 * w)) ^ i = (2 ^ w) ^ (2 * i)
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    have hB_pow2 : (x >>> w) / B ^ i = x / (2 ^ w) ^ (2 * i + 1) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, hB_pow1, pow_succ']
    rw [hB_pow2, hB_pow1]
  rw [Finset.sum_congr rfl hterm]
  clear hterm hno_carry hblock_lt a b
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma fieldSum_swarPopcountUp (k : ℕ) (hk : k ≤ 16) (x : ℕ) :
    fieldSum k (swarPopcountUp k x) = fieldSum 0 x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold swarPopcountUp
    rw [fieldSum_swarStep (by omega), ih (by omega)]

lemma card_filter_testBit_le_swarPopcountUp (x : ℕ) :
    ((Finset.range 65536).filter (fun i => x.testBit i = true)).card ≤ swarPopcountUp 16 x := by
  have h0 : fieldSum 0 x = ((Finset.range 65536).filter (fun i => x.testBit i = true)).card := by
    unfold fieldSum
    have h1 : 2 ^ (16 - 0) = 65536 := by norm_num
    rw [h1, Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pow_zero, pow_one, testBit_eq_decide_div_mod]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]
  have h16 : fieldSum 16 (swarPopcountUp 16 x) = (swarPopcountUp 16 x) % 2 ^ 65536 := by
    unfold fieldSum
    have h1 : 2 ^ (16 - 16) = 1 := by norm_num
    have h2 : 2 ^ 16 = 65536 := by norm_num
    rw [h1, h2, Finset.sum_range_one, pow_zero, Nat.div_one]
  calc
    ((Finset.range 65536).filter (fun i => x.testBit i = true)).card
        = fieldSum 0 x := h0.symm
    _ = fieldSum 16 (swarPopcountUp 16 x) := (fieldSum_swarPopcountUp 16 (le_refl 16) x).symm
    _ = (swarPopcountUp 16 x) % 2 ^ 65536 := h16
    _ ≤ swarPopcountUp 16 x := Nat.mod_le _ _

/-- Kernel-reduced GMP computation: the 60-prime bitmask sieve on odd integers `< 83341`
leaves exactly `8134` survivors. Zero `native_decide`, pure definitional `rfl`! -/
lemma swarPopcountUp_survivorMask : swarPopcountUp 16 survivorMask = 8134 := rfl

/-- **Unconditional 8,135th odd prime count bound**: there are at most `8134` (hence `< 8135`)
odd primes below `83341`. -/
theorem odd_prime_card_lt_83341 :
    ((Finset.range 83341).filter (fun p => Nat.Prime p ∧ Odd p)).card < 8135 := by
  have hle :
      ((Finset.range 83341).filter (fun p => Nat.Prime p ∧ Odd p)).card ≤
        ((Finset.range 65536).filter (fun i => survivorMask.testBit i = true)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp ⊢
      dsimp only
      exact ⟨by omega, survivorMask_testBit_of_odd_prime hp.2.1 hp.2.2 hp.1⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
      rcases hp₁.2.2 with ⟨t₁, rfl⟩
      rcases hp₂.2.2 with ⟨t₂, rfl⟩
      dsimp only at heq
      omega
  have hpop := card_filter_testBit_le_swarPopcountUp survivorMask
  rw [swarPopcountUp_survivorMask] at hpop
  omega

/-- **Unconditional 8,135th odd prime lower bound**: every finite set of at least `8135`
odd primes contains a prime `≥ 83341`. -/
theorem odd_prime_8135_ge_83341 {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ Odd p) (hcard : 8135 ≤ Q.card) :
    ∃ p ∈ Q, 83341 ≤ p := by
  by_contra hnot
  push Not at hnot
  have hsub : Q ⊆ (Finset.range 83341).filter (fun p => Nat.Prime p ∧ Odd p) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hnot p hp, hQ p hp⟩
  have hle := Finset.card_le_card hsub
  have hlt := odd_prime_card_lt_83341
  omega

/-! ### Part 3: Lemma C (Instantiated) and 8,138-Prime Corollary -/

/-- **Lemma C (Instantiated, `ceiling-1.md` Section 3)**:
Parameterized explicitly by `hN1` (the `N₁ ≥ 8135` bound from the externally dual-graded
`gi-lw-1` depth-6 Lemma W certificate), every normal odd prime set with reciprocal sum `> 2`
has at least `91,476` members (`8135 + 83341 = 91476`). -/
theorem lemma_C_91476
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    91476 ≤ P.card :=
  lemma_C_general hN1 odd_prime_card_lt_83341 hP hsum

/-- **8,138-Prime Corollary (`ceiling-1.md` Section 3)**:
Parameterized explicitly by `hN1` (the `N₁ ≥ 8135` bound from the externally dual-graded
`gi-lw-1` depth-6 Lemma W certificate), every counterexample to Giuga's conjecture has
at least `8,138` prime factors (combining `hN1`, `lemma_C_91476`, and K7 `m ≡ v + 1 [MOD 4]`). -/
theorem cor_giuga_8138_primes
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {n : ℕ} (hn : IsGiugaCounterexample n) :
    8138 ≤ n.primeFactors.card := by
  have hn2 : 2 ≤ n := hn.1
  obtain ⟨v, ⟨hv1, hv_eq⟩, _⟩ := giuga_exists_value hn
  have hnorm : IsNormalOddPrimeSet n.primeFactors := giuga_primeFactors_normal hn
  have hrecip := giuga_recip_sum_eq hn hv_eq
  rcases lt_or_ge v 2 with hv_lt2 | hv_ge2
  · have hv_one : v = 1 := by omega
    subst hv_one
    have h8135 : 8135 ≤ n.primeFactors.card := hN1 n.primeFactors hnorm (giuga_recip_sum_gt_one hn)
    have hmod4 : n.primeFactors.card ≡ 1 + 1 [MOD 4] :=
      odd_giuga_card_mod_four (giuga_odd hn) (giuga_squarefree hn) hv_eq
    have hrem : n.primeFactors.card % 4 = 2 := by
      simpa [Nat.ModEq] using hmod4
    omega
  · have hgt2 : (2 : ℝ) < ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) := by
      rw [hrecip]
      have hvR : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv_ge2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hn_pos
      linarith
    have h91476 : 91476 ≤ n.primeFactors.card := lemma_C_91476 hN1 hnorm hgt2
    omega

/-! ### Part 4: Section 4 Rules (100% Unconditional) -/

/-- Helper: pairing off-diagonal elements `(p, q)` with `p ≠ q` into `p < q` and `q < p`. -/
lemma prod_offDiag_eq_prod_lt {α : Type*} [CommMonoid α] (P : Finset ℕ) (f : ℕ → ℕ → α) :
    (∏ p ∈ P, ∏ q ∈ P.erase p, f p q) =
      ∏ x ∈ (P ×ˢ P).filter (fun x => x.1 < x.2), (f x.1 x.2 * f x.2 x.1) := by
  have h1 : (∏ p ∈ P, ∏ q ∈ P.erase p, f p q) =
      ∏ x ∈ (P ×ˢ P).filter (fun x => x.1 ≠ x.2), f x.1 x.2 := by
    rw [Finset.prod_filter, Finset.prod_product]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Finset.prod_filter]
    have hfilt : P.erase p = P.filter (fun a => p ≠ a) := by
      ext a
      simp [Finset.mem_erase, ne_comm, and_comm]
    exact Finset.prod_congr hfilt (fun _ _ => rfl)
  rw [h1]
  set A := (P ×ˢ P).filter (fun x => x.1 < x.2)
  set B := (P ×ˢ P).filter (fun x => x.2 < x.1)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1' : x.1 < x.2 := (Finset.mem_filter.mp hxA).2
    have h2' : x.2 < x.1 := (Finset.mem_filter.mp hxB).2
    omega
  have hunion : A ∪ B = (P ×ˢ P).filter (fun x => x.1 ≠ x.2) := by
    ext ⟨a, b⟩
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro (⟨h, hlt⟩ | ⟨h, hgt⟩) <;> exact ⟨h, by omega⟩
    · rintro ⟨h, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨h, hgt⟩
  rw [← hunion, Finset.prod_union hdisj, Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [A, B, Finset.mem_filter, Finset.mem_product] at hx ⊢
    exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
  · intro x₁ _ x₂ _ h
    ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  · intro y hy
    refine ⟨(y.2, y.1), ?_, rfl⟩
    simp only [A, B, Finset.mem_filter, Finset.mem_product] at hy ⊢
    exact ⟨⟨hy.1.2, hy.1.1⟩, hy.2⟩
  · intro _ _; rfl

/-- Helper: cardinality of `{(p, q) ∈ S ×ˢ S | p < q}` equals `S.card * (S.card - 1) / 2`. -/
lemma card_filter_lt_prod (S : Finset ℕ) :
    ((S ×ˢ S).filter (fun x => x.1 < x.2)).card = S.card * (S.card - 1) / 2 := by
  set A := (S ×ˢ S).filter (fun x => x.1 < x.2)
  set B := (S ×ˢ S).filter (fun x => x.2 < x.1)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 : x.1 < x.2 := (Finset.mem_filter.mp hxA).2
    have h2 : x.2 < x.1 := (Finset.mem_filter.mp hxB).2
    omega
  have hunion : A ∪ B = S.offDiag := by
    ext ⟨a, b⟩
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨ha, hb⟩, hlt⟩ | ⟨⟨ha, hb⟩, hgt⟩) <;> exact ⟨ha, hb, by omega⟩
    · rintro ⟨ha, hb, hne⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨⟨ha, hb⟩, hlt⟩
      · exact Or.inr ⟨⟨ha, hb⟩, hgt⟩
  have hAB : A.card = B.card := by
    refine Finset.card_bij (fun x _ => (x.2, x.1)) ?_ ?_ ?_
    · intro x hx
      simp only [A, B, Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨hx.1.2, hx.1.1⟩, hx.2⟩
    · intro x₁ _ x₂ _ h
      ext
      · exact congrArg Prod.snd h
      · exact congrArg Prod.fst h
    · intro y hy
      refine ⟨(y.2, y.1), ?_, rfl⟩
      simp only [A, B, Finset.mem_filter, Finset.mem_product] at hy ⊢
      exact ⟨⟨hy.1.2, hy.1.1⟩, hy.2⟩
  have hsum : A.card + B.card = S.card * S.card - S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.offDiag_card]
  have h2A : 2 * A.card = S.card * (S.card - 1) := by
    rw [Nat.mul_sub_one]
    omega
  omega

/-- **Section 4 Reciprocity Rule (100% unconditional, via Quadratic Reciprocity)**:
For every Giuga counterexample `n`, the number `k` of prime factors `p ∣ n` with
`p ≡ 3 [MOD 4]` satisfies `k % 4 = 0 ∨ k % 4 = 1`. -/
theorem giuga_reciprocity_rule {n : ℕ} (hn : IsGiugaCounterexample n) :
    (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 ∨
      (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 1 := by
  have hn2 : 2 ≤ n := hn.1
  have hG := ((giuga_iff_carmichael_and_giuga hn2 hn.2.1).mp hn).2
  have hodd : Odd n := giuga_odd hn
  have hprod : n = ∏ p ∈ n.primeFactors, p := giuga_prod_primeFactors hn
  set P := n.primeFactors
  have hP_prime : ∀ p ∈ P, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hP_odd : ∀ p ∈ P, Odd p := fun p hp => Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  have hP_ne2 : ∀ p ∈ P, p ≠ 2 := fun p hp => by
    rcases hP_odd p hp with ⟨k, hk⟩; omega
  let leg : ℕ → ℕ → ℤ := fun p q =>
    if h : Nat.Prime p then @legendreSym p ⟨h⟩ (q : ℤ) else 0
  have hleg_def : ∀ p q, (hp : Nat.Prime p) → leg p q = @legendreSym p ⟨hp⟩ (q : ℤ) := by
    intro p q hp
    simp only [leg, hp, ↓reduceDIte]
  have hleg_one : ∀ p ∈ P, ∏ q ∈ P.erase p, leg p q = 1 := by
    intro p hp
    have hpr : Nat.Prime p := hP_prime p hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpr⟩
    have hnp_eq : n / p = ∏ q ∈ P.erase p, q := by
      have hmul : p * (n / p) = p * ∏ q ∈ P.erase p, q := by
        rw [Nat.mul_div_cancel' hdvd, hprod, Finset.mul_prod_erase P (fun x => x) hp]
      exact Nat.eq_of_mul_eq_mul_left hpr.pos hmul
    have hq_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpr.pos
    have hmod1 : (((n / p : ℕ) : ℤ) : ZMod p) = 1 := by
      have hz : ((n / p - 1 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ p).mpr (hG p hpr hdvd)
      rw [Nat.cast_sub hq_pos, Nat.cast_one, sub_eq_zero] at hz
      rw [Int.cast_natCast, hz]
    have hleg : legendreSym p ((n / p : ℕ) : ℤ) = 1 := by
      rw [legendreSym.eq_one_iff]
      · refine ⟨1, ?_⟩
        rw [one_mul, hmod1]
      · rw [hmod1]
        exact one_ne_zero
    rw [hnp_eq, Nat.cast_prod] at hleg
    have hprod_hom :
        legendreSym p (∏ q ∈ P.erase p, (q : ℤ)) =
          ∏ q ∈ P.erase p, legendreSym p (q : ℤ) :=
      map_prod (legendreSym.hom p) (f := fun q : ℕ => (q : ℤ)) (s := P.erase p)
    rw [hprod_hom] at hleg
    calc
      ∏ q ∈ P.erase p, leg p q
          = ∏ q ∈ P.erase p, legendreSym p (q : ℤ) :=
            Finset.prod_congr rfl fun q _ => hleg_def p q hpr
      _ = 1 := hleg
  have hdouble : (∏ p ∈ P, ∏ q ∈ P.erase p, leg p q) = 1 := by
    rw [Finset.prod_congr rfl hleg_one, Finset.prod_const_one]
  rw [prod_offDiag_eq_prod_lt] at hdouble
  have hqr : ∀ x ∈ (P ×ˢ P).filter (fun x => x.1 < x.2),
      leg x.1 x.2 * leg x.2 x.1 =
        if x.1 % 4 = 3 ∧ x.2 % 4 = 3 then (-1 : ℤ) else 1 := by
    intro ⟨p, q⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_product] at hmem
    rcases hmem with ⟨⟨hp, hq⟩, hlt⟩
    have hpr : Nat.Prime p := hP_prime p hp
    have hqr' : Nat.Prime q := hP_prime q hq
    have : Fact p.Prime := ⟨hpr⟩
    have : Fact q.Prime := ⟨hqr'⟩
    have hp2 : p ≠ 2 := hP_ne2 p hp
    have hq2 : q ≠ 2 := hP_ne2 q hq
    rw [hleg_def p q hpr, hleg_def q p hqr']
    have hrec := legendreSym.quadratic_reciprocity' hp2 hq2
    have hsq : legendreSym p (q : ℤ) * legendreSym p (q : ℤ) = 1 := by
      have hndvd : ¬ ((p : ℤ) ∣ (q : ℤ)) := by
        intro h
        have hd : p ∣ q := Int.ofNat_dvd.mp h
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpr hqr').mp hd
        omega
      have hne : ((q : ℤ) : ZMod p) ≠ 0 := by
        intro hz
        exact hndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd (q : ℤ) p).mp hz)
      rcases legendreSym.eq_one_or_neg_one (p := p) hne with h1 | h1 <;> simp [h1]
    have hmul_rec : legendreSym p (q : ℤ) * legendreSym q (p : ℤ) =
        (-1 : ℤ) ^ (p / 2 * (q / 2)) := by
      calc
        legendreSym p (q : ℤ) * legendreSym q (p : ℤ)
            = legendreSym p (q : ℤ) *
                ((-1 : ℤ) ^ (p / 2 * (q / 2)) * legendreSym p (q : ℤ)) := by
              rw [hrec]
        _ = (-1 : ℤ) ^ (p / 2 * (q / 2)) * (legendreSym p (q : ℤ) * legendreSym p (q : ℤ)) := by
              ring
        _ = (-1 : ℤ) ^ (p / 2 * (q / 2)) := by rw [hsq, mul_one]
    rw [hmul_rec]
    have hp_odd : Odd p := hP_odd p hp
    have hq_odd : Odd q := hP_odd q hq
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by rcases hp_odd with ⟨t, rfl⟩; omega
    have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by rcases hq_odd with ⟨t, rfl⟩; omega
    split_ifs with h33
    · have hodd_prod : Odd (p / 2 * (q / 2)) := by
        have h1 : Odd (p / 2) := Nat.odd_iff.mpr (by omega)
        have h2 : Odd (q / 2) := Nat.odd_iff.mpr (by omega)
        exact h1.mul h2
      exact hodd_prod.neg_one_pow
    · have heven_prod : Even (p / 2 * (q / 2)) := by
        rcases hp4 with hp1 | hp3
        · have h1 : Even (p / 2) := Nat.even_iff.mpr (by omega)
          exact h1.mul_right _
        · have hq1 : q % 4 = 1 := by
            rcases hq4 with h | h
            · exact h
            · exfalso; exact h33 ⟨hp3, h⟩
          have h2 : Even (q / 2) := Nat.even_iff.mpr (by omega)
          exact h2.mul_left _
      exact heven_prod.neg_one_pow
  rw [Finset.prod_congr rfl hqr] at hdouble
  set P₃ := P.filter (fun p => p % 4 = 3)
  have hfilt_eq :
      ((P ×ˢ P).filter (fun x => x.1 < x.2)).filter (fun x => x.1 % 4 = 3 ∧ x.2 % 4 = 3) =
        (P₃ ×ˢ P₃).filter (fun x => x.1 < x.2) := by
    ext ⟨a, b⟩
    simp only [P₃, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, hfilt_eq,
    card_filter_lt_prod] at hdouble
  set k := P₃.card
  have heven : Even (k * (k - 1) / 2) := by
    by_contra hnot
    have hodd_k : Odd (k * (k - 1) / 2) := Nat.not_even_iff_odd.mp hnot
    rw [hodd_k.neg_one_pow] at hdouble
    omega
  rcases heven with ⟨t, ht⟩
  have hmod : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    have hq : k = 4 * (k / 4) + 2 := by omega
    set r := k / 4
    have hcalc : k * (k - 1) / 2 = (2 * r + 1) * (4 * r + 1) := by
      rw [hq]
      have : (4 * r + 2) * (4 * r + 2 - 1) = 2 * ((2 * r + 1) * (4 * r + 1)) := by
        have hsub : 4 * r + 2 - 1 = 4 * r + 1 := by omega
        rw [hsub]; ring
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [hcalc] at ht
    have hodd_lhs : ((2 * r + 1) * (4 * r + 1)) % 2 = 1 := by
      have ha : (2 * r + 1) % 2 = 1 := by omega
      have hb : (4 * r + 1) % 2 = 1 := by omega
      rw [Nat.mul_mod, ha, hb]
    omega
  · exfalso
    have hq : k = 4 * (k / 4) + 3 := by omega
    set r := k / 4
    have hcalc : k * (k - 1) / 2 = (4 * r + 3) * (2 * r + 1) := by
      rw [hq]
      have : (4 * r + 3) * (4 * r + 3 - 1) = 2 * ((4 * r + 3) * (2 * r + 1)) := by
        have hsub : 4 * r + 3 - 1 = 4 * r + 2 := by omega
        rw [hsub]; ring
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    rw [hcalc] at ht
    have hodd_lhs : ((4 * r + 3) * (2 * r + 1)) % 2 = 1 := by
      have ha : (4 * r + 3) % 2 = 1 := by omega
      have hb : (2 * r + 1) % 2 = 1 := by omega
      rw [Nat.mul_mod, ha, hb]
    omega

/-- Helper: in `ZMod 8`, every odd natural number squares to `1`. -/
lemma odd_sq_zmod8 {x : ℕ} (hx : Odd x) : (x : ZMod 8) ^ 2 = 1 := by
  rcases hx with ⟨k, rfl⟩
  have h : (2 * k + 1 : ℕ) % 8 = 1 ∨ (2 * k + 1 : ℕ) % 8 = 3 ∨
      (2 * k + 1 : ℕ) % 8 = 5 ∨ (2 * k + 1 : ℕ) % 8 = 7 := by omega
  rcases h with h1 | h3 | h5 | h7
  · rw [← ZMod.natCast_mod, h1]; decide
  · rw [← ZMod.natCast_mod, h3]; decide
  · rw [← ZMod.natCast_mod, h5]; decide
  · rw [← ZMod.natCast_mod, h7]; decide

/-- **Section 4 Residue Rule mod 8 (100% unconditional)**:
For every Giuga counterexample `n` with value `v` (`∑ p ∈ n.primeFactors, n / p = v * n + 1`),
`(∑ p ∈ n.primeFactors, p) ≡ v + n [MOD 8]`. -/
theorem giuga_residue_mod_8 {n v : ℕ} (hn : IsGiugaCounterexample n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    (∑ p ∈ n.primeFactors, p) ≡ v + n [MOD 8] := by
  have hodd : Odd n := giuga_odd hn
  set P := n.primeFactors
  have hP_odd : ∀ p ∈ P, Odd p := fun p hp =>
    Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  have hdiv_zmod : ∀ p ∈ P, ((n / p : ℕ) : ZMod 8) = (n : ZMod 8) * (p : ZMod 8) := by
    intro p hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hmul : (p : ZMod 8) * ((n / p : ℕ) : ZMod 8) = (n : ZMod 8) := by
      have := congrArg (Nat.cast : ℕ → ZMod 8) (Nat.mul_div_cancel' hdvd)
      simpa [Nat.cast_mul] using this
    have hpsq : (p : ZMod 8) ^ 2 = 1 := odd_sq_zmod8 (hP_odd p hp)
    calc
      ((n / p : ℕ) : ZMod 8) = (p : ZMod 8) ^ 2 * ((n / p : ℕ) : ZMod 8) := by rw [hpsq, one_mul]
      _ = (p : ZMod 8) * ((p : ZMod 8) * ((n / p : ℕ) : ZMod 8)) := by ring
      _ = (p : ZMod 8) * (n : ZMod 8) := by rw [hmul]
      _ = (n : ZMod 8) * (p : ZMod 8) := mul_comm _ _
  have hv_zmod : (∑ p ∈ P, ((n / p : ℕ) : ZMod 8)) = (v : ZMod 8) * (n : ZMod 8) + 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod 8) hv
    simpa [Nat.cast_sum, Nat.cast_add, Nat.cast_mul] using this
  rw [Finset.sum_congr rfl hdiv_zmod, ← Finset.mul_sum] at hv_zmod
  have hnsq : (n : ZMod 8) ^ 2 = 1 := odd_sq_zmod8 hodd
  have hkey : ((∑ p ∈ P, p : ℕ) : ZMod 8) = ((v + n : ℕ) : ZMod 8) := by
    rw [Nat.cast_sum, Nat.cast_add]
    have hmul := congrArg (fun x => (n : ZMod 8) * x) hv_zmod
    calc
      (∑ p ∈ P, (p : ZMod 8))
          = (n : ZMod 8) ^ 2 * (∑ p ∈ P, (p : ZMod 8)) := by rw [hnsq, one_mul]
      _ = (n : ZMod 8) * ((n : ZMod 8) * ∑ p ∈ P, (p : ZMod 8)) := by ring
      _ = (n : ZMod 8) * ((v : ZMod 8) * (n : ZMod 8) + 1) := hmul
      _ = (v : ZMod 8) * (n : ZMod 8) ^ 2 + (n : ZMod 8) := by ring
      _ = (v : ZMod 8) + (n : ZMod 8) := by rw [hnsq, mul_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ 8).mp hkey

/-- **Section 4 Exactness Rule (100% unconditional)**:
For every Giuga counterexample `n` of value `v = 1` (`∑ p ∈ n.primeFactors, n / p = n + 1`)
and every `p ∈ n.primeFactors`, `(∑ q ∈ n.primeFactors, (1 : ℝ) / q) - 1 < 1 / (p : ℝ)`. -/
theorem giuga_exactness_rule {n : ℕ} (hn : IsGiugaCounterexample n)
    (hv1 : ∑ p ∈ n.primeFactors, n / p = n + 1)
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    (∑ q ∈ n.primeFactors, (1 : ℝ) / (q : ℝ)) - 1 < 1 / (p : ℝ) := by
  have hv1' : ∑ q ∈ n.primeFactors, n / q = 1 * n + 1 := by simpa using hv1
  have hrecip := giuga_recip_sum_eq hn hv1'
  have hcard : 2 ≤ n.primeFactors.card := giuga_two_le_card hn
  have hne : (n.primeFactors.erase p).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
    omega
  obtain ⟨q, hq_er⟩ := hne
  have hq_ne : q ≠ p := (Finset.mem_erase.mp hq_er).1
  have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq_er).2
  have hpr_p := Nat.prime_of_mem_primeFactors hp
  have hpr_q := Nat.prime_of_mem_primeFactors hq_mem
  have hdvd_p := Nat.dvd_of_mem_primeFactors hp
  have hdvd_q := Nat.dvd_of_mem_primeFactors hq_mem
  have hcop : Nat.Coprime p q := (hpr_p.coprime_iff_not_dvd).mpr fun h =>
    hq_ne ((Nat.prime_dvd_prime_iff_eq hpr_p hpr_q).mp h).symm
  have hpq_dvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hdvd_p hdvd_q
  have hn2 : 2 ≤ n := hn.1
  have hpq_le : p * q ≤ n := Nat.le_of_dvd (by omega) hpq_dvd
  have hlt_n : p < n := by
    have hq2 : 2 ≤ q := hpr_q.two_le
    have hp2 : 2 ≤ p := hpr_p.two_le
    nlinarith
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr_p.pos
  have hlt_nR : (p : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hlt_n
  have hinv : (1 : ℝ) / (n : ℝ) < 1 / (p : ℝ) := one_div_lt_one_div_of_lt hp_pos hlt_nR
  rw [hrecip]
  simpa [one_div] using hinv

end Giuga
