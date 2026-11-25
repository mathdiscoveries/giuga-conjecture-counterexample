module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Giuga's Conjecture: Definitions and Classical Reductions (K1, K2, K3, K7)

Faithful Lean 4 formalization of Giuga's 1950 conjecture, Giuga's equivalence (K1),
structural properties of counterexamples (K2), reciprocal characterization and value (K3),
and the Borwein–Borwein–Borwein–Girgensohn (1996) parity rule `m ≡ v + 1 (mod 4)` (K7).
-/

@[expose] public section

namespace Giuga

open scoped BigOperators

/-- A composite integer `n ≥ 2` is a **counterexample to Giuga's conjecture (1950)**
when `∑_{k=1}^{n-1} k^(n-1) ≡ n - 1 [MOD n]`. -/
def IsGiugaCounterexample (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ Nat.Prime n ∧ (∑ k ∈ Finset.Ico 1 n, k ^ (n - 1)) ≡ n - 1 [MOD n]

/-- **Carmichael (Korselt) divisibility condition**: for every prime `p ∣ n`,
`(p - 1) ∣ (n / p - 1)`. -/
def IsCarmichaelCondition (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → (p - 1) ∣ (n / p - 1)

/-- **Giuga divisibility condition**: for every prime `p ∣ n`, `p ∣ (n / p - 1)`. -/
def IsGiugaCondition (n : ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1)

/-- A finite set `P` of odd primes is **normal** when no prime `q ∈ P` divides `r - 1`
for any larger prime `r ∈ P`. -/
def IsNormalOddPrimeSet (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p ∧ Odd p) ∧ (∀ q ∈ P, ∀ r ∈ P, q < r → ¬ (q ∣ r - 1))

/-- Any subset of a normal odd prime set is a normal odd prime set. -/
theorem IsNormalOddPrimeSet.subset {P Q : Finset ℕ} (hP : IsNormalOddPrimeSet P) (hQ : Q ⊆ P) :
    IsNormalOddPrimeSet Q :=
  ⟨fun p hp => hP.1 p (hQ hp), fun q hq r hr hlt => hP.2 q (hQ hq) r (hQ hr) hlt⟩

/-- For a normal odd prime set, no element divides any element minus `1` (without needing `q < r`). -/
theorem IsNormalOddPrimeSet.not_dvd_sub_one {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    {q r : ℕ} (hq : q ∈ P) (hr : r ∈ P) : ¬ (q ∣ r - 1) := by
  rcases lt_trichotomy q r with hlt | rfl | hgt
  · exact hP.2 q hq r hr hlt
  · intro hdvd
    have hq2 : 2 ≤ q := (hP.1 q hq).1.two_le
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro hdvd
    have hr2 : 2 ≤ r := (hP.1 r hr).1.two_le
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega

/-! ### K1: Prime power-sum lemma and Giuga's reduction -/

/-- Helper: when `f 0 = 0` and `0 < m`, summing `f` over `Ico 1 m` equals summing over `range m`. -/
lemma sum_Ico_one_eq_sum_range {M : Type*} [AddCommMonoid M] {f : ℕ → M} {m : ℕ}
    (hm : 0 < m) (hf0 : f 0 = 0) :
    (∑ k ∈ Finset.Ico 1 m, f k) = ∑ k ∈ Finset.range m, f k := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm, hf0, zero_add]

/-- **Prime power-sum lemma (K1 helper)**: for a prime `p` and exponent `e ≥ 1`,
`∑_{j=1}^{p-1} j^e` in `ZMod p` equals `-1` if `(p - 1) ∣ e` and `0` otherwise. -/
theorem prime_pow_sum_zmod (p : ℕ) [Fact p.Prime] (e : ℕ) (he : 1 ≤ e) :
    (∑ j ∈ Finset.Ico 1 p, (j : ZMod p) ^ e) = if (p - 1) ∣ e then -1 else 0 := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have : NeZero p := ⟨hp.ne_zero⟩
  have hsum_range :
      (∑ j ∈ Finset.Ico 1 p, (j : ZMod p) ^ e) = ∑ x : ZMod p, x ^ e := by
    rw [sum_Ico_one_eq_sum_range (M := ZMod p) hp_pos (by simp [zero_pow (by omega : e ≠ 0)])]
    refine Finset.sum_bij (fun j _ => (j : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro j₁ hj₁ j₂ hj₂ heq
      have h1 : j₁ < p := Finset.mem_range.mp hj₁
      have h2 : j₂ < p := Finset.mem_range.mp hj₂
      have hmod : j₁ % p = j₂ % p := (ZMod.natCast_eq_natCast_iff' j₁ j₂ p).mp heq
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    · intro x _
      exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  rw [hsum_range]
  split_ifs with hdvd
  · rcases hdvd with ⟨k, rfl⟩
    have hsum_erase : (∑ x : ZMod p, x ^ ((p - 1) * k)) =
        ∑ x ∈ Finset.univ.erase (0 : ZMod p), x ^ ((p - 1) * k) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
      have h0 : (0 : ZMod p) ^ ((p - 1) * k) = 0 := zero_pow (by omega)
      rw [h0, zero_add]
    rw [hsum_erase]
    have hterm : ∀ x ∈ Finset.univ.erase (0 : ZMod p), x ^ ((p - 1) * k) = (1 : ZMod p) := by
      intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx0, one_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime hp]
    have hge_ne : ((g : ZMod p) ^ e) ≠ 1 := by
      intro hEq
      have hg_pow : g ^ e = 1 := by
        ext
        simpa [Units.val_pow_eq_pow_val] using hEq
      have hd : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one hg_pow
      rw [hord] at hd
      exact hdvd hd
    have hmul : ((g : ZMod p) ^ e) * (∑ x : ZMod p, x ^ e) = ∑ x : ZMod p, x ^ e := by
      rw [Finset.mul_sum]
      have hrew : ∀ x : ZMod p, (g : ZMod p) ^ e * x ^ e = ((g : ZMod p) * x) ^ e := fun x =>
        (mul_pow (g : ZMod p) x e).symm
      simp_rw [hrew]
      exact Fintype.sum_equiv (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero) _ _ (fun _ => rfl)
    have hzero : ((g : ZMod p) ^ e - 1) * (∑ x : ZMod p, x ^ e) = 0 := by
      rw [sub_mul, one_mul, hmul, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hge_ne)

/-- Power sum `∑_{k=1}^{n-1} k^(n-1)` evaluated in `ZMod p` for a prime `p ∣ n`. -/
theorem pow_sum_zmod_of_dvd {n p : ℕ} (hn : 2 ≤ n) (hp : Nat.Prime p) (hdvd : p ∣ n) :
    (∑ k ∈ Finset.Ico 1 n, (k : ZMod p) ^ (n - 1)) =
      if (p - 1) ∣ (n - 1) then -((n / p : ℕ) : ZMod p) else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  set q := n / p
  have hnq : n = p * q := (Nat.mul_div_cancel' hdvd).symm
  have he : 1 ≤ n - 1 := by omega
  have hsum_range : (∑ k ∈ Finset.Ico 1 n, (k : ZMod p) ^ (n - 1)) =
      ∑ k ∈ Finset.range (p * q), (k : ZMod p) ^ (n - 1) := by
    rw [← hnq]
    exact sum_Ico_one_eq_sum_range (by omega) (by simp [zero_pow (by omega : n - 1 ≠ 0)])
  rw [hsum_range]
  have hsplit : (∑ k ∈ Finset.range (p * q), (k : ZMod p) ^ (n - 1)) =
      (q : ZMod p) * ∑ j ∈ Finset.range p, (j : ZMod p) ^ (n - 1) := by
    have hprod : ∑ k ∈ Finset.range (p * q), (k : ZMod p) ^ (n - 1) =
        ∑ i ∈ Finset.range q, ∑ j ∈ Finset.range p, ((i * p + j : ℕ) : ZMod p) ^ (n - 1) := by
      induction q with
      | zero => simp
      | succ q' ih =>
        rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, ih]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    rw [hprod]
    have hinner : ∀ i ∈ Finset.range q,
        (∑ j ∈ Finset.range p, ((i * p + j : ℕ) : ZMod p) ^ (n - 1)) =
          ∑ j ∈ Finset.range p, (j : ZMod p) ^ (n - 1) := by
      intro i _
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Nat.cast_add, Nat.cast_mul]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  rw [← sum_Ico_one_eq_sum_range hp.pos (by simp [zero_pow (by omega : n - 1 ≠ 0)]),
    prime_pow_sum_zmod p (n - 1) he]
  split_ifs <;> ring

/-- Helper: for `p ∣ n` with `p ≥ 2` and `n ≥ 1`, `(p - 1) ∣ (n - 1) ↔ (p - 1) ∣ (n / p - 1)`. -/
lemma sub_one_dvd_sub_one_iff {n p : ℕ} (hn : 1 ≤ n) (hp : 2 ≤ p) (hdvd : p ∣ n) :
    (p - 1) ∣ (n - 1) ↔ (p - 1) ∣ (n / p - 1) := by
  have hq : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have heq : n - 1 = (p - 1) * (n / p) + (n / p - 1) := by
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hdvd
    zify [hn, (by omega : 1 ≤ p), hq]
    have hmulZ : (p : ℤ) * (n / p : ℕ) = (n : ℤ) := by exact_mod_cast hmul
    linarith
  rw [heq]
  exact Nat.dvd_add_right (dvd_mul_right (p - 1) (n / p))

/-- Any `n ≥ 1` satisfying `IsGiugaCondition n` is squarefree. -/
theorem squarefree_of_giuga_condition {n : ℕ} (hn : 1 ≤ n) (hG : IsGiugaCondition n) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hp_dvd : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hq_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp.pos
  have hp_dvd_q : p ∣ n / p := by
    rcases hpp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : p * (n / p) = p * (p * k) := by
      rw [Nat.mul_div_cancel' hp_dvd, hk, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hp.pos this
  have hp_dvd_q1 : p ∣ n / p - 1 := hG p hp hp_dvd
  have hp_dvd_one : p ∣ 1 := by
    have hsub : p ∣ (n / p) - (n / p - 1) := Nat.dvd_sub hp_dvd_q hp_dvd_q1
    have h1 : n / p - (n / p - 1) = 1 := by omega
    rwa [h1] at hsub
  exact hp.not_dvd_one hp_dvd_one

/-- Helper: if `a ≡ b [MOD p]` for every `p ∈ S` of distinct primes, then `a ≡ b [MOD ∏ p ∈ S, p]`. -/
lemma modEq_prod_of_forall_mem {a b : ℕ} {S : Finset ℕ}
    (hP : ∀ p ∈ S, Nat.Prime p) (hmod : ∀ p ∈ S, a ≡ b [MOD p]) :
    a ≡ b [MOD ∏ p ∈ S, p] := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : Nat.Prime p := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hmod_s : a ≡ b [MOD ∏ q ∈ s, q] := ih hs (fun q hq => hmod q (Finset.mem_insert_of_mem hq))
    have hmod_p : a ≡ b [MOD p] := hmod p (Finset.mem_insert_self p s)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : Nat.Prime q := hs q hq
      refine (hp.coprime_iff_not_dvd).mpr fun hdiv => ?_
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hdiv
      exact hps (heq ▸ hq)
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmod_p, hmod_s⟩

/-- **K1 (Giuga 1950; BBBG 1996, Theorem 1)**: For composite `n ≥ 2`,
`IsGiugaCounterexample n ↔ IsCarmichaelCondition n ∧ IsGiugaCondition n`. -/
theorem giuga_iff_carmichael_and_giuga {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ Nat.Prime n) :
    IsGiugaCounterexample n ↔ IsCarmichaelCondition n ∧ IsGiugaCondition n := by
  constructor
  · rintro ⟨_, _, hcong⟩
    have hboth : ∀ p, Nat.Prime p → p ∣ n → (p - 1) ∣ (n / p - 1) ∧ p ∣ (n / p - 1) := by
      intro p hp hdvd
      have : Fact p.Prime := ⟨hp⟩
      have hmodp : (∑ k ∈ Finset.Ico 1 n, k ^ (n - 1)) ≡ n - 1 [MOD p] := hcong.of_dvd hdvd
      have hzmod : (∑ k ∈ Finset.Ico 1 n, (k : ZMod p) ^ (n - 1)) = ((n - 1 : ℕ) : ZMod p) := by
        have := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hmodp
        simpa [Nat.cast_sum, Nat.cast_pow] using this
      have hrhs : ((n - 1 : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hdvd
        rw [hn0, zero_sub]
      rw [pow_sum_zmod_of_dvd hn hp hdvd, hrhs] at hzmod
      have hpm1 : (p - 1) ∣ (n - 1) := by
        by_contra hnot
        simp only [hnot, ↓reduceIte] at hzmod
        have h10 : (1 : ZMod p) = 0 := by
          have := congrArg Neg.neg hzmod
          simpa using this.symm
        exact one_ne_zero h10
      simp only [hpm1, ↓reduceIte] at hzmod
      have hq1 : ((n / p : ℕ) : ZMod p) = 1 := neg_inj.mp hzmod
      have hq_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
      have hp_dvd_q1 : p ∣ n / p - 1 := by
        rw [← ZMod.natCast_eq_zero_iff]
        rw [Nat.cast_sub hq_pos, hq1, Nat.cast_one, sub_self]
      exact ⟨(sub_one_dvd_sub_one_iff (by omega) hp.two_le hdvd).mp hpm1, hp_dvd_q1⟩
    exact ⟨fun p hp hdvd => (hboth p hp hdvd).1, fun p hp hdvd => (hboth p hp hdvd).2⟩
  · rintro ⟨hC, hG⟩
    refine ⟨hn, hnp, ?_⟩
    have hsq : Squarefree n := squarefree_of_giuga_condition (by omega) hG
    have hprod : ∏ p ∈ n.primeFactors, p = n := Nat.prod_primeFactors_of_squarefree hsq
    have hmod_prod : (∑ k ∈ Finset.Ico 1 n, k ^ (n - 1)) ≡ n - 1 [MOD ∏ p ∈ n.primeFactors, p] := by
      refine modEq_prod_of_forall_mem (fun p hp => Nat.prime_of_mem_primeFactors hp) ?_
      intro p hp_mem
      have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
      have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.natCast_eq_natCast_iff]
      simp only [Nat.cast_sum, Nat.cast_pow]
      rw [pow_sum_zmod_of_dvd hn hp hdvd]
      have hpm1 : (p - 1) ∣ (n - 1) :=
        (sub_one_dvd_sub_one_iff (by omega) hp.two_le hdvd).mpr (hC p hp hdvd)
      simp only [hpm1, ↓reduceIte]
      have hq_pos : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
      have hq1 : ((n / p : ℕ) : ZMod p) = 1 := by
        have hz : ((n / p - 1 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ p).mpr (hG p hp hdvd)
        rw [Nat.cast_sub hq_pos, Nat.cast_one, sub_eq_zero] at hz
        exact hz
      rw [hq1, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hdvd
      rw [hn0, zero_sub]
    rwa [hprod] at hmod_prod

/-! ### K2: Structural properties of Giuga counterexamples -/

/-- **K2(a)**: Every Giuga counterexample is squarefree. -/
theorem giuga_squarefree {n : ℕ} (hn : IsGiugaCounterexample n) : Squarefree n := by
  have hn2 : 2 ≤ n := hn.1
  have hG := ((giuga_iff_carmichael_and_giuga hn2 hn.2.1).mp hn).2
  exact squarefree_of_giuga_condition (by omega) hG

/-- **K2(b)**: Every Giuga counterexample equals the product of its prime factors. -/
theorem giuga_prod_primeFactors {n : ℕ} (hn : IsGiugaCounterexample n) :
    n = ∏ p ∈ n.primeFactors, p :=
  (Nat.prod_primeFactors_of_squarefree (giuga_squarefree hn)).symm

/-- **K2(c)**: Every Giuga counterexample has at least `2` prime factors. -/
theorem giuga_two_le_card {n : ℕ} (hn : IsGiugaCounterexample n) :
    2 ≤ n.primeFactors.card := by
  have hn2 : 2 ≤ n := hn.1
  have hprod := giuga_prod_primeFactors hn
  by_contra hlt
  have hle : n.primeFactors.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · have hemp : n.primeFactors = ∅ := Finset.card_eq_zero.mp h0
    rw [hemp, Finset.prod_empty] at hprod
    omega
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
    rw [hp, Finset.prod_singleton] at hprod
    exact hn.2.1 (hprod ▸ hp_prime)

/-- **K2(d)**: Every Giuga counterexample is odd. -/
theorem giuga_odd {n : ℕ} (hn : IsGiugaCounterexample n) : Odd n := by
  have hn2 : 2 ≤ n := hn.1
  have hC := ((giuga_iff_carmichael_and_giuga hn2 hn.2.1).mp hn).1
  by_contra hnot
  have heven : Even n := Nat.not_odd_iff_even.mp hnot
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
  have hcard : 2 ≤ n.primeFactors.card := giuga_two_le_card hn
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, by omega⟩
  have hne : (n.primeFactors.erase 2).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem h2mem]
    omega
  obtain ⟨p, hp_er⟩ := hne
  have hp_ne2 : p ≠ 2 := (Finset.mem_erase.mp hp_er).1
  have hp_mem : p ∈ n.primeFactors := (Finset.mem_erase.mp hp_er).2
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_mem
  have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
  have hp_odd : Odd p := hp.odd_of_ne_two hp_ne2
  have h2_pm1 : 2 ∣ p - 1 := by
    rcases hp_odd with ⟨k, rfl⟩
    exact ⟨k, by omega⟩
  have hpm1_nm1 : (p - 1) ∣ (n - 1) :=
    (sub_one_dvd_sub_one_iff (by omega) hp.two_le hpdvd).mpr (hC p hp hpdvd)
  have h2_nm1 : 2 ∣ n - 1 := dvd_trans h2_pm1 hpm1_nm1
  have h2_1 : 2 ∣ 1 := by
    have hsub := Nat.dvd_sub h2dvd h2_nm1
    have : n - (n - 1) = 1 := by omega
    rwa [this] at hsub
  omega

/-- **K2(e)**: The prime factors of every Giuga counterexample form a normal odd prime set. -/
theorem giuga_primeFactors_normal {n : ℕ} (hn : IsGiugaCounterexample n) :
    IsNormalOddPrimeSet n.primeFactors := by
  have hn2 : 2 ≤ n := hn.1
  have hC := ((giuga_iff_carmichael_and_giuga hn2 hn.2.1).mp hn).1
  have hodd : Odd n := giuga_odd hn
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    exact ⟨hpr, Odd.of_dvd_nat hodd hdvd⟩
  · intro q hq r hr _ hq_dvd
    have hq_pr := Nat.prime_of_mem_primeFactors hq
    have hr_pr := Nat.prime_of_mem_primeFactors hr
    have hq_dvd_n := Nat.dvd_of_mem_primeFactors hq
    have hr_dvd_n := Nat.dvd_of_mem_primeFactors hr
    have hr_dvd_nm1 : (r - 1) ∣ (n - 1) :=
      (sub_one_dvd_sub_one_iff (by omega) hr_pr.two_le hr_dvd_n).mpr (hC r hr_pr hr_dvd_n)
    have hq_dvd_nm1 : q ∣ n - 1 := dvd_trans hq_dvd hr_dvd_nm1
    have hq_dvd_1 : q ∣ 1 := by
      have hsub := Nat.dvd_sub hq_dvd_n hq_dvd_nm1
      have : n - (n - 1) = 1 := by omega
      rwa [this] at hsub
    exact hq_pr.not_dvd_one hq_dvd_1

/-! ### K3: Value and reciprocal sum equation -/

/-- Helper: if every `p ∈ S` of distinct primes divides `m`, then `∏ p ∈ S, p ∣ m`. -/
lemma prod_dvd_of_forall_dvd {m : ℕ} {S : Finset ℕ}
    (hP : ∀ p ∈ S, Nat.Prime p) (hdvd : ∀ p ∈ S, p ∣ m) :
    (∏ p ∈ S, p) ∣ m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp : Nat.Prime p := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : Nat.Prime q := hs q hq
      refine (hp.coprime_iff_not_dvd).mpr fun hdiv => ?_
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hdiv
      exact hps (heq ▸ hq)
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (Finset.mem_insert_self p s))
      (ih hs (fun q hq => hdvd q (Finset.mem_insert_of_mem hq)))

/-- **K3(a)**: Every Giuga counterexample `n` has a unique integer value `v ≥ 1` such that
`∑ p ∈ n.primeFactors, n / p = v * n + 1`. -/
theorem giuga_exists_value {n : ℕ} (hn : IsGiugaCounterexample n) :
    ∃! v : ℕ, 1 ≤ v ∧ ∑ p ∈ n.primeFactors, n / p = v * n + 1 := by
  have hn2 : 2 ≤ n := hn.1
  have hG := ((giuga_iff_carmichael_and_giuga hn2 hn.2.1).mp hn).2
  have hprod := giuga_prod_primeFactors hn
  have hcard := giuga_two_le_card hn
  have hsum_ge2 : 2 ≤ ∑ p ∈ n.primeFactors, n / p := by
    calc
      2 ≤ n.primeFactors.card := hcard
      _ = ∑ _p ∈ n.primeFactors, 1 := by simp
      _ ≤ ∑ p ∈ n.primeFactors, n / p := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpr := Nat.prime_of_mem_primeFactors hp
        have hdvd := Nat.dvd_of_mem_primeFactors hp
        exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpr.pos
  have hdvd_each : ∀ p ∈ n.primeFactors, p ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hsplit : ∑ q ∈ n.primeFactors, n / q =
        (∑ q ∈ n.primeFactors.erase p, n / q) + n / p := by
      rw [add_comm]
      exact (Finset.add_sum_erase _ _ hp).symm
    have hqp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hpr.pos
    rw [hsplit, Nat.add_sub_assoc hqp]
    refine Nat.dvd_add ?_ (hG p hpr hpdvd)
    refine Finset.dvd_sum fun q hq => ?_
    have hne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq).2
    have hq_pr := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd := Nat.dvd_of_mem_primeFactors hq_mem
    have hcop : Nat.Coprime p q := (hpr.coprime_iff_not_dvd).mpr fun h =>
      hne ((Nat.prime_dvd_prime_iff_eq hpr hq_pr).mp h).symm
    have hpq_dvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hpdvd hq_dvd
    rcases hpq_dvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : q * (n / q) = q * (p * k) := by
      rw [Nat.mul_div_cancel' hq_dvd, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left hq_pr.pos this
  have hn_dvd : n ∣ (∑ q ∈ n.primeFactors, n / q) - 1 := by
    have hdiv := prod_dvd_of_forall_dvd (fun p hp => Nat.prime_of_mem_primeFactors hp) hdvd_each
    rwa [← hprod] at hdiv
  rcases hn_dvd with ⟨v, hv⟩
  have hsum_eq : ∑ q ∈ n.primeFactors, n / q = v * n + 1 := by
    rw [mul_comm]
    omega
  have hv1 : 1 ≤ v := by
    by_contra h0
    have hv0 : v = 0 := by omega
    rw [hv0, zero_mul, zero_add] at hsum_eq
    omega
  refine ⟨v, ⟨hv1, hsum_eq⟩, ?_⟩
  rintro v' ⟨_, hv'⟩
  have hmul : v' * n = v * n := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < n) hmul

/-- **K3(b)**: Equivalently, `∑ p ∈ n.primeFactors, (1 : ℝ) / p = (v : ℝ) + 1 / (n : ℝ)`. -/
theorem giuga_recip_sum_eq {n v : ℕ} (hn : IsGiugaCounterexample n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) = (v : ℝ) + 1 / (n : ℝ) := by
  have hn2 : 2 ≤ n := hn.1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : (∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℝ)) = (v : ℝ) * (n : ℝ) + 1 := by
    exact_mod_cast hv
  have hterm : ∀ p ∈ n.primeFactors, ((n / p : ℕ) : ℝ) / (n : ℝ) = (1 : ℝ) / (p : ℝ) := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
    have hmul : (p : ℝ) * ((n / p : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    field_simp [hn0, hp0]
    linarith
  calc
    ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℝ) / (n : ℝ) :=
          Finset.sum_congr rfl (fun p hp => (hterm p hp).symm)
    _ = (∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℝ)) / (n : ℝ) := (Finset.sum_div _ _ _).symm
    _ = ((v : ℝ) * (n : ℝ) + 1) / (n : ℝ) := by rw [hcast]
    _ = (v : ℝ) + 1 / (n : ℝ) := by field_simp [hn0]

/-- **K3(c)**: Every Giuga counterexample has reciprocal prime sum strictly greater than `1`. -/
theorem giuga_recip_sum_gt_one {n : ℕ} (hn : IsGiugaCounterexample n) :
    (1 : ℝ) < ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) := by
  have hn2 : 2 ≤ n := hn.1
  obtain ⟨v, ⟨hv1, hv_eq⟩, _⟩ := giuga_exists_value hn
  rw [giuga_recip_sum_eq hn hv_eq]
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hn_pos
  linarith

/-! ### K7: Mod-4 count rule for odd squarefree Giuga numbers -/

/-- Helper: in `ZMod 4`, every odd natural number squares to `1`. -/
lemma odd_sq_zmod4 {x : ℕ} (hx : Odd x) : (x : ZMod 4) ^ 2 = 1 := by
  rcases hx with ⟨k, rfl⟩
  have h : (2 * k + 1 : ℕ) % 4 = 1 ∨ (2 * k + 1 : ℕ) % 4 = 3 := by omega
  rcases h with h1 | h3
  · have hc : ((2 * k + 1 : ℕ) : ZMod 4) = 1 := by
      rw [← ZMod.natCast_mod, h1]; rfl
    rw [hc]; decide
  · have hc : ((2 * k + 1 : ℕ) : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, h3]; rfl
    rw [hc]; decide

/-- Helper: in `ZMod 4`, `2 * k + (-1)^k = 1` for all `k : ℕ`. -/
lemma two_mul_add_neg_one_pow_zmod4 (k : ℕ) :
    (2 : ZMod 4) * (k : ZMod 4) + (-1 : ZMod 4) ^ k = 1 := by
  have hsq : (-1 : ZMod 4) ^ 2 = 1 := by decide
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have hpow : (-1 : ZMod 4) ^ (j + j) = 1 := by
      rw [← two_mul, pow_mul, hsq, one_pow]
    have h2 : (2 : ZMod 4) * ((j + j : ℕ) : ZMod 4) = 0 := by
      push_cast
      have : (2 : ZMod 4) * (j + j) = (4 : ZMod 4) * j := by ring
      rw [this]; change (0 : ZMod 4) * j = 0; simp
    rw [hpow, h2, zero_add]
  · have hpow : (-1 : ZMod 4) ^ (2 * j + 1) = -1 := by
      rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
    have h2 : (2 : ZMod 4) * ((2 * j + 1 : ℕ) : ZMod 4) = 2 := by
      push_cast
      have : (2 : ZMod 4) * (2 * j + 1) = (4 : ZMod 4) * j + 2 := by ring
      rw [this]; change (0 : ZMod 4) * j + 2 = 2; simp
    rw [hpow, h2]; decide

/-- **K7 (BBBG 1996)**: For any odd squarefree `n` with `∑ p ∈ n.primeFactors, n / p = v * n + 1`,
`n.primeFactors.card ≡ v + 1 [MOD 4]`. -/
theorem odd_giuga_card_mod_four {n v : ℕ} (hodd : Odd n) (hsq : Squarefree n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    n.primeFactors.card ≡ v + 1 [MOD 4] := by
  set P := n.primeFactors
  set P₃ := P.filter (fun p => p % 4 = 3)
  set P₁ := P.filter (fun p => ¬ (p % 4 = 3))
  have hP_odd : ∀ p ∈ P, Odd p := fun p hp =>
    Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  have hP₃_val : ∀ p ∈ P₃, (p : ZMod 4) = -1 := by
    intro p hp
    have h3 : p % 4 = 3 := (Finset.mem_filter.mp hp).2
    rw [← ZMod.natCast_mod, h3]; decide
  have hP₁_val : ∀ p ∈ P₁, (p : ZMod 4) = 1 := by
    intro p hp
    have hmem := (Finset.mem_filter.mp hp).1
    have hne3 : p % 4 ≠ 3 := (Finset.mem_filter.mp hp).2
    have ho : Odd p := hP_odd p hmem
    have h1 : p % 4 = 1 := by
      rcases ho with ⟨k, rfl⟩; omega
    rw [← ZMod.natCast_mod, h1]; decide
  have hprod_n : (n : ZMod 4) = (-1 : ZMod 4) ^ P₃.card := by
    have hpn : n = ∏ p ∈ P, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    conv_lhs => rw [hpn]
    rw [Nat.cast_prod, ← Finset.prod_filter_mul_prod_filter_not P (fun p => p % 4 = 3)]
    have h3prod : (∏ p ∈ P₃, (p : ZMod 4)) = (-1 : ZMod 4) ^ P₃.card := by
      rw [Finset.prod_congr rfl hP₃_val, Finset.prod_const]
    have h1prod : (∏ p ∈ P₁, (p : ZMod 4)) = 1 := by
      rw [Finset.prod_congr rfl hP₁_val, Finset.prod_const, one_pow]
    rw [h3prod, h1prod, mul_one]
  have hsum_p : (∑ p ∈ P, (p : ZMod 4)) = (P.card : ZMod 4) - 2 * (P₃.card : ZMod 4) := by
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p % 4 = 3)]
    have h3sum : (∑ p ∈ P₃, (p : ZMod 4)) = -((P₃.card : ZMod 4)) := by
      rw [Finset.sum_congr rfl hP₃_val, Finset.sum_const, nsmul_eq_mul]; ring
    have h1sum : (∑ p ∈ P₁, (p : ZMod 4)) = (P₁.card : ZMod 4) := by
      rw [Finset.sum_congr rfl hP₁_val, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard_add : P₃.card + P₁.card = P.card :=
      Finset.card_filter_add_card_filter_not (fun p => p % 4 = 3)
    have hcard_cast : (P₃.card : ZMod 4) + (P₁.card : ZMod 4) = (P.card : ZMod 4) := by
      have := congrArg (Nat.cast : ℕ → ZMod 4) hcard_add
      simpa [Nat.cast_add] using this
    rw [h3sum, h1sum]
    linear_combination hcard_cast
  have hdiv_zmod : ∀ p ∈ P, ((n / p : ℕ) : ZMod 4) = (n : ZMod 4) * (p : ZMod 4) := by
    intro p hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hmul : (p : ZMod 4) * ((n / p : ℕ) : ZMod 4) = (n : ZMod 4) := by
      have := congrArg (Nat.cast : ℕ → ZMod 4) (Nat.mul_div_cancel' hdvd)
      simpa [Nat.cast_mul] using this
    have hpsq : (p : ZMod 4) ^ 2 = 1 := odd_sq_zmod4 (hP_odd p hp)
    calc
      ((n / p : ℕ) : ZMod 4) = (p : ZMod 4) ^ 2 * ((n / p : ℕ) : ZMod 4) := by rw [hpsq, one_mul]
      _ = (p : ZMod 4) * ((p : ZMod 4) * ((n / p : ℕ) : ZMod 4)) := by ring
      _ = (p : ZMod 4) * (n : ZMod 4) := by rw [hmul]
      _ = (n : ZMod 4) * (p : ZMod 4) := mul_comm _ _
  have hv_zmod : (∑ p ∈ P, ((n / p : ℕ) : ZMod 4)) = (v : ZMod 4) * (n : ZMod 4) + 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod 4) hv
    simpa [Nat.cast_sum, Nat.cast_add, Nat.cast_mul] using this
  rw [Finset.sum_congr rfl hdiv_zmod, ← Finset.mul_sum] at hv_zmod
  have hnsq : (n : ZMod 4) ^ 2 = 1 := odd_sq_zmod4 hodd
  have hkey : (∑ p ∈ P, (p : ZMod 4)) = (v : ZMod 4) + (n : ZMod 4) := by
    have hmul := congrArg (fun x => (n : ZMod 4) * x) hv_zmod
    calc
      (∑ p ∈ P, (p : ZMod 4))
          = (n : ZMod 4) ^ 2 * (∑ p ∈ P, (p : ZMod 4)) := by rw [hnsq, one_mul]
      _ = (n : ZMod 4) * ((n : ZMod 4) * ∑ p ∈ P, (p : ZMod 4)) := by ring
      _ = (n : ZMod 4) * ((v : ZMod 4) * (n : ZMod 4) + 1) := hmul
      _ = (v : ZMod 4) * (n : ZMod 4) ^ 2 + (n : ZMod 4) := by ring
      _ = (v : ZMod 4) + (n : ZMod 4) := by rw [hnsq, mul_one]
  rw [hsum_p, hprod_n] at hkey
  have hfinal : (P.card : ZMod 4) = ((v + 1 : ℕ) : ZMod 4) := by
    rw [Nat.cast_add, Nat.cast_one]
    have h1 := two_mul_add_neg_one_pow_zmod4 P₃.card
    linear_combination hkey + h1
  exact (ZMod.natCast_eq_natCast_iff _ _ 4).mp hfinal

end Giuga
