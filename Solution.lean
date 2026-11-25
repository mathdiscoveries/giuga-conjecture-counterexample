module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.ModEq
public import Giuga

/-!
# Palomar Solution: Lower Bounds and Local Ceilings for Giuga's Conjecture

Discharges all 21 compared declarations of `Challenge.lean` via the verified
`Giuga` library with zero `sorry`, zero `native_decide`, and standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) only.
-/

@[expose] public section

namespace GiugaChallenge

open scoped BigOperators

/-- A composite integer `n ≥ 2` is a counterexample to Giuga's conjecture when
`∑_{k=1}^{n-1} k^(n-1) ≡ n - 1 [MOD n]`. -/
def IsGiugaCounterexample (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ Nat.Prime n ∧ (∑ k ∈ Finset.Ico 1 n, k ^ (n - 1)) ≡ n - 1 [MOD n]

/-- A finite set `P` of odd primes is normal when no prime `q ∈ P` divides `r - 1`
for any larger prime `r ∈ P`. -/
def IsNormalOddPrimeSet (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p ∧ Odd p) ∧ (∀ q ∈ P, ∀ r ∈ P, q < r → ¬ (q ∣ r - 1))

/-- Remaining reciprocal mass needed past a fixed prefix `S`: `need S = 1 - ∑_{s ∈ S} 1/s`. -/
noncomputable def need (S : Finset ℕ) : ℝ :=
  1 - ∑ s ∈ S, (1 : ℝ) / (s : ℝ)

/-- Two primes `q < r` form a conflict edge when `q ∣ r - 1`. -/
def IsConflictEdge (q r : ℕ) : Prop :=
  q < r ∧ q ∣ r - 1

/-- `x` is a tail prime of leaf `(p_d, S)` when `x` is an odd prime with `p_d ≤ x`
and `¬ (s ∣ x - 1)` for every `s ∈ S`. -/
def IsTailPrime (S : Finset ℕ) (p_d x : ℕ) : Prop :=
  Nat.Prime x ∧ Odd x ∧ p_d ≤ x ∧ ∀ s ∈ S, ¬ (s ∣ x - 1)

/-- The edge-dual upper bound on vertex set `U`, edge set `E`, vertex weights `w`,
and dual edge variables `η`. -/
noncomputable def edgeDualUB (U : Finset ℕ) (E : Finset (ℕ × ℕ))
    (w : ℕ → ℝ) (η : ℕ × ℕ → ℝ) : ℝ :=
  (∑ e ∈ E, η e) +
    ∑ v ∈ U, max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e)

/-- Least integer `K' ≥ K` satisfying `sCard + K' ≡ 2 [MOD 4]`. -/
def routeALiftK (sCard K : ℕ) : ℕ :=
  K + (6 - (sCard + K) % 4) % 4

/-- Unconditional 575-prime lower bound for any normal odd prime set with reciprocal sum `> 1`. -/
theorem unconditional_normal_set_575 {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    575 ≤ P.card :=
  Giuga.unconditional_normal_set_575 hP hsum

/-- Unconditional 578-prime lower bound for every counterexample to Giuga's conjecture. -/
theorem giuga_unconditional_578_primes {n : ℕ} (hn : IsGiugaCounterexample n) :
    578 ≤ n.primeFactors.card :=
  Giuga.giuga_unconditional_578_primes hn

/-- Unconditional 1,804-digit lower bound (`10 ^ 1803 < n`) for every Giuga counterexample. -/
theorem giuga_unconditional_gt_10_pow_1803 {n : ℕ} (hn : IsGiugaCounterexample n) :
    10 ^ 1803 < n :=
  Giuga.giuga_unconditional_gt_10_pow_1803 hn

/-- Unconditional existence of an 8,135-element normal odd prime set with reciprocal sum `> 1`
and product strictly between `10 ^ 40732` and `10 ^ 40733` (`40,733` decimal digits). -/
theorem exists_normal_odd_prime_set_8135 :
    ∃ G : Finset ℕ, IsNormalOddPrimeSet G ∧ G.card = 8135 ∧
      (1 : ℚ) < (∑ p ∈ G, (1 : ℚ) / (p : ℚ)) ∧
      (1 : ℝ) < (∑ p ∈ G, (1 : ℝ) / (p : ℝ)) ∧
      10 ^ 40732 < (∏ p ∈ G, p) ∧ (∏ p ∈ G, p) < 10 ^ 40733 :=
  Giuga.exists_normal_odd_prime_set_8135

/-- Unconditional existence of an 8,138-element normal odd prime set satisfying all seven
local Giuga counterexample rules simultaneously, with product between `10 ^ 40750` and
`10 ^ 40751` (`40,751` decimal digits). -/
theorem exists_ceiling_witness_8138 :
    ∃ W : Finset ℕ,
      IsNormalOddPrimeSet W ∧
      W.card = 8138 ∧
      3 ∉ W ∧
      (1 : ℝ) < (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) ∧
      (∀ p ∈ W, (∑ q ∈ W.erase p, (1 : ℝ) / (q : ℝ)) ≤ 1) ∧
      ((W.filter (fun p => p % 4 = 3)).card % 4 = 0 ∨
        (W.filter (fun p => p % 4 = 3)).card % 4 = 1) ∧
      (∑ p ∈ W, p) ≡ 1 + (∏ p ∈ W, p) [MOD 8] ∧
      10 ^ 40750 < (∏ p ∈ W, p) ∧
      (∏ p ∈ W, p) < 10 ^ 40751 :=
  Giuga.exists_ceiling_witness_8138

/-- Lemma W, Form (E) (Edge-Dual Count Bound). -/
theorem lemma_w_edge_dual_count {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d : ℕ} {Λ : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hΛ : 0 < Λ)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < Λ → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    Λ * (need S - edgeDualUB U E (fun x => (1 : ℝ) / (x : ℝ) - 1 / Λ) η) < (T.card : ℝ) :=
  Giuga.lemma_w_edge_dual_count hT hTail hneed hΛ hU hE hη

/-- Lemma W, Form (E) (Edge-Dual Product / Log Bound). -/
theorem lemma_w_edge_dual_prod {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d : ℕ} {Λ μ : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hΛ : 1 ≤ Λ)
    (hμ0 : 0 < μ)
    (hμ : μ ≤ Λ * Real.log Λ)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < Λ → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    μ * need S - edgeDualUB U E (fun x => μ / (x : ℝ) - Real.log (x : ℝ)) η <
      ∑ x ∈ T, Real.log (x : ℝ) :=
  Giuga.lemma_w_edge_dual_prod hT hTail hneed hΛ hμ0 hμ hU hE hη

/-- Complete Frontier Theorem combining Lemma W Form (E) count certificates across all
normal prefixes below `p_d`. -/
theorem lemma_w_frontier_count {p_d : ℕ} {F : Finset (Finset ℕ)}
    (hF : ∀ S : Finset ℕ, IsNormalOddPrimeSet S → (∀ s ∈ S, s < p_d) → S ∈ F)
    (Λ : Finset ℕ → ℝ) (U : Finset ℕ → Finset ℕ) (E : Finset ℕ → Finset (ℕ × ℕ))
    (η : Finset ℕ → ℕ × ℕ → ℝ) (B : Finset ℕ → ℕ)
    (hΛ : ∀ S ∈ F, 0 < Λ S)
    (hU : ∀ S ∈ F, ∀ x, IsTailPrime S p_d x → (x : ℝ) < Λ S → x ∈ U S)
    (hE : ∀ S ∈ F, ∀ e ∈ E S, e.1 ∈ U S ∧ e.2 ∈ U S ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ S ∈ F, ∀ e ∈ E S, 0 ≤ η S e)
    (hB : ∀ S ∈ F, (B S : ℝ) - 1 ≤
      Λ S * (need S - edgeDualUB (U S) (E S) (fun x => (1 : ℝ) / (x : ℝ) - 1 / Λ S) (η S)))
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    F.inf' ⟨∅, hF ∅ ⟨fun _ h => False.elim (Finset.notMem_empty _ h),
        fun _ h => False.elim (Finset.notMem_empty _ h)⟩
        (fun _ h => False.elim (Finset.notMem_empty _ h))⟩
        (fun S => S.card + B S) ≤ P.card :=
  Giuga.lemma_w_frontier_count hF Λ U E η B hΛ hU hE hη hB hP hsum

/-- Lemma W, Refinement 2 (strict `>` form when `0 < μ`). -/
theorem lemma_w_refinement2_strict {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d K : ℕ} {μ ν C : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hK : K ≤ T.card)
    (hμ : 0 < μ) (hν : 0 ≤ ν) (hC : 0 < C)
    (hfC : μ / C + ν - Real.log C ≤ 0)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < C → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    μ * need S + ν * (K : ℝ) -
        edgeDualUB U E (fun x => μ / (x : ℝ) + ν - Real.log (x : ℝ)) η <
      ∑ x ∈ T, Real.log (x : ℝ) :=
  Giuga.lemma_w_refinement2_strict hT hTail hneed hK hμ hν hC hfC hU hE hη

/-- Lemma W Refinement 2 with Route (a) modulo-4 linear lift. -/
theorem lemma_w_refinement2_route_a {P U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d K : ℕ} {μ ν C : ℝ} {η : ℕ × ℕ → ℝ}
    (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ))
    (hmod4 : P.card ≡ 2 [MOD 4])
    (hK : K ≤ (P.filter (p_d ≤ ·)).card)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hC : 0 < C)
    (hfC : μ / C + ν - Real.log C ≤ 0)
    (hU : ∀ x, IsTailPrime (P.filter (· < p_d)) p_d x → (x : ℝ) < C → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    let S := P.filter (· < p_d)
    let K' := routeALiftK S.card K
    (∑ s ∈ S, Real.log (s : ℝ)) + μ * need S + ν * (K' : ℝ) -
        edgeDualUB U E (fun x => μ / (x : ℝ) + ν - Real.log (x : ℝ)) η ≤
      Real.log (∏ p ∈ P, (p : ℝ)) :=
  Giuga.lemma_w_refinement2_route_a hP hsum hmod4 hK hμ hν hC hfC hU hE hη

/-- General Lemma C: threshold-1 normal-set bound `N₁` and `#{odd primes < q} < N₁`
imply `N₁ + q ≤ P.card` whenever `∑_{p ∈ P} 1/p > 2`. -/
theorem lemma_C_general {N₁ q : ℕ}
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      N₁ ≤ P.card)
    (hq : ((Finset.range q).filter (fun p => Nat.Prime p ∧ Odd p)).card < N₁)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    N₁ + q ≤ P.card :=
  Giuga.lemma_C_general hN1 hq hP hsum

/-- Unconditional 8,135th odd prime lower bound: every finite set of at least `8,135` odd primes
contains a prime `≥ 83,341`. -/
theorem odd_prime_8135_ge_83341 {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, Nat.Prime p ∧ Odd p) (hcard : 8135 ≤ Q.card) :
    ∃ p ∈ Q, 83341 ≤ p :=
  Giuga.odd_prime_8135_ge_83341 hQ hcard

/-- Unconditional quadratic-reciprocity obstruction: the count of prime factors `p ≡ 3 [MOD 4]`
of any Giuga counterexample is congruent to `0` or `1` modulo `4`. -/
theorem giuga_reciprocity_rule {n : ℕ} (hn : IsGiugaCounterexample n) :
    (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 ∨
      (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 1 :=
  Giuga.giuga_reciprocity_rule hn

/-- Unconditional modulo-8 residue rule: `∑ p ≡ v + n [MOD 8]` for every Giuga counterexample
of value `v`. -/
theorem giuga_residue_mod_8 {n v : ℕ} (hn : IsGiugaCounterexample n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    (∑ p ∈ n.primeFactors, p) ≡ v + n [MOD 8] :=
  Giuga.giuga_residue_mod_8 hn hv

/-- Unconditional exactness rule at value `v = 1`: `(∑ 1/q) - 1 < 1/p` for every `p ∣ n`. -/
theorem giuga_exactness_rule {n : ℕ} (hn : IsGiugaCounterexample n)
    (hv1 : ∑ p ∈ n.primeFactors, n / p = n + 1)
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    (∑ q ∈ n.primeFactors, (1 : ℝ) / (q : ℝ)) - 1 < 1 / (p : ℝ) :=
  Giuga.giuga_exactness_rule hn hv1 hp

/-- Unconditional modulo-8 count congruence: `n.primeFactors.card ≡ v + 1 [MOD 8]` for every
Giuga counterexample `n` of value `v`. -/
theorem giuga_card_mod_eight {n v : ℕ} (hn : IsGiugaCounterexample n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    n.primeFactors.card ≡ v + 1 [MOD 8] :=
  Giuga.giuga_card_mod_eight hn hv

/-- Instantiated Lemma C (parameterized by `hN1`): every normal odd prime set with
reciprocal sum `> 2` has at least `91,476` primes. -/
theorem lemma_C_91476
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    91476 ≤ P.card :=
  Giuga.lemma_C_91476 hN1 hP hsum

/-- Conditional 8,138-prime counterexample bound (parameterized by `hN1`). -/
theorem cor_giuga_8138_primes
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {n : ℕ} (hn : IsGiugaCounterexample n) :
    8138 ≤ n.primeFactors.card :=
  Giuga.cor_giuga_8138_primes hN1 hn

/-- Conditional 36,084-digit counterexample bound (`10 ^ 36083 < n`) from `hN1` alone,
with zero external logarithm-certificate hypotheses. -/
theorem cor_giuga_gt_10_pow_36083
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {n : ℕ} (hn : IsGiugaCounterexample n) :
    10 ^ 36083 < n :=
  Giuga.cor_giuga_gt_10_pow_36083 hN1 hn

/-- Conditional Lemma C product bound (`10 ^ 446177 < ∏ P`) for reciprocal sum `> 2`,
parameterized by `hN1`. -/
theorem lemma_C_prod_gt_10_pow_446177
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    10 ^ 446177 < ∏ p ∈ P, p :=
  Giuga.lemma_C_prod_gt_10_pow_446177 hN1 hP hsum

/-- Conditional 40,748-digit counterexample bound (`10 ^ 40747 < n`), parameterized by `hN1`
and the depth-6 Route (a) frontier certificate hypotheses. -/
theorem cor_giuga_route_a_gt_10_pow_40747
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {F : Finset (Finset ℕ)}
    (hF : ∀ S : Finset ℕ, IsNormalOddPrimeSet S → (∀ s ∈ S, s < 17) → S ∈ F)
    (K : Finset ℕ → ℕ)
    (μ ν C : Finset ℕ → ℝ)
    (U : Finset ℕ → Finset ℕ)
    (E : Finset ℕ → Finset (ℕ × ℕ))
    (η : Finset ℕ → ℕ × ℕ → ℝ)
    (hTailK : ∀ P : Finset ℕ, IsNormalOddPrimeSet P →
      (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      K (P.filter (· < 17)) ≤ (P.filter (17 ≤ ·)).card)
    (hCert : ∀ S ∈ F,
      0 ≤ μ S ∧ 0 ≤ ν S ∧ 0 < C S ∧
      μ S / C S + ν S - Real.log (C S) ≤ 0 ∧
      (∀ x, IsTailPrime S 17 x → (x : ℝ) < C S → x ∈ U S) ∧
      (∀ e ∈ E S, e.1 ∈ U S ∧ e.2 ∈ U S ∧ IsConflictEdge e.1 e.2) ∧
      (∀ e ∈ E S, 0 ≤ η S e) ∧
      (40747 : ℝ) * Real.log 10 <
        (∑ s ∈ S, Real.log (s : ℝ)) + μ S * need S +
          ν S * (routeALiftK S.card (K S) : ℝ) -
          edgeDualUB (U S) (E S) (fun x => μ S / (x : ℝ) + ν S - Real.log (x : ℝ)) (η S))
    {n : ℕ} (hn : IsGiugaCounterexample n) :
    10 ^ 40747 < n :=
  Giuga.cor_giuga_route_a_gt_10_pow_40747 hN1 hF K μ ν C U E η hTailK hCert hn

end GiugaChallenge
