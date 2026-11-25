module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Giuga.Defs

import Mathlib.Tactic

/-!
# Lemma W (Forest & Edge-Dual Forms, Frontier, Refinements 1 & 2, Hand Case)

Faithful Lean 4 formalization of the Giuga pod's weighted independent-set / edge-dual
relaxations (`lemma-w-1.md` and `lemma-w-2.md`):
- Core edge-dual upper bound `edge_dual_le_ub`;
- Forest forms `(F1)` (`lemma_w_forest_count`) and `(F2)` (`lemma_w_forest_prod`);
- Edge-dual forms `(E)` (`lemma_w_edge_dual_count`, `lemma_w_edge_dual_prod`);
- Complete frontier theorem (`lemma_w_frontier_count`);
- Refinement 1 (`Λ / v - 1` count weights and exact scaling identity);
- Refinement 2 (`μ / x + ν - ln x` size bound, both `≥` and strict `>` when `μ > 0`);
- Unconditional hand case proving `|P| ≥ 9` for every normal odd prime set with `∑ 1/p > 1`
  (and hence `≥ 9` prime factors for every Giuga counterexample).
-/

@[expose] public section

namespace Giuga

open scoped BigOperators

/-! ### Core definitions -/

/-- Remaining reciprocal mass needed past a fixed prefix `S`: `need S = 1 - ∑_{s ∈ S} 1/s`. -/
noncomputable def need (S : Finset ℕ) : ℝ :=
  1 - ∑ s ∈ S, (1 : ℝ) / (s : ℝ)

/-- Two primes `q < r` form a **conflict edge** when `q ∣ r - 1`. -/
def IsConflictEdge (q r : ℕ) : Prop :=
  q < r ∧ q ∣ r - 1

/-- `x` is a **tail prime** of leaf `(p_d, S)` when `x` is an odd prime with `p_d ≤ x`
and `¬ (s ∣ x - 1)` for every `s ∈ S`. -/
def IsTailPrime (S : Finset ℕ) (p_d x : ℕ) : Prop :=
  Nat.Prime x ∧ Odd x ∧ p_d ≤ x ∧ ∀ s ∈ S, ¬ (s ∣ x - 1)

/-- A vertex subset `A` is **independent** with respect to edge set `E` when no edge of `E`
has both endpoints in `A`. -/
def IsIndependent (E : Finset (ℕ × ℕ)) (A : Finset ℕ) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ A ∧ e.2 ∈ A)

instance instDecidableIsIndependent (E : Finset (ℕ × ℕ)) (A : Finset ℕ) :
    Decidable (IsIndependent E A) := by
  unfold IsIndependent
  infer_instance

/-- The **edge-dual upper bound** on vertex set `U`, edge set `E`, vertex weights `w`,
and dual edge variables `η`:
`UB(U, E, w, η) = ∑_{e ∈ E} η_e + ∑_{v ∈ U} max(0, w_v - ∑_{e ∋ v} η_e)`. -/
noncomputable def edgeDualUB (U : Finset ℕ) (E : Finset (ℕ × ℕ))
    (w : ℕ → ℝ) (η : ℕ × ℕ → ℝ) : ℝ :=
  (∑ e ∈ E, η e) +
    ∑ v ∈ U, max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e)

lemma empty_mem_indepPowerset (V : Finset ℕ) (E : Finset (ℕ × ℕ)) :
    ∅ ∈ V.powerset.filter (fun A => IsIndependent E A) := by
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.empty_subset V, fun _ _ h => by simp at h⟩

/-- **Maximum-weight independent set** (`MWIS`) value over vertex set `V`, edge set `E`,
and vertex weight function `w`. The empty set is always independent, so `0 ≤ mwis V E w`. -/
noncomputable def mwis (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (w : ℕ → ℝ) : ℝ :=
  (V.powerset.filter (fun A => IsIndependent E A)).sup'
    ⟨∅, empty_mem_indepPowerset V E⟩ (fun A => ∑ x ∈ A, w x)

lemma le_mwis {V : Finset ℕ} {E : Finset (ℕ × ℕ)} {w : ℕ → ℝ} {A : Finset ℕ}
    (hsub : A ⊆ V) (hind : IsIndependent E A) :
    (∑ x ∈ A, w x) ≤ mwis V E w := by
  unfold mwis
  refine Finset.le_sup' (f := fun B => ∑ x ∈ B, w x) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hind⟩

lemma zero_le_mwis (V : Finset ℕ) (E : Finset (ℕ × ℕ)) (w : ℕ → ℝ) :
    0 ≤ mwis V E w := by
  simpa using le_mwis (Finset.empty_subset V) (fun _ _ h => by simp at h)

/-! ### Normal sets, conflict independence, and leaf splitting -/

/-- Any normal odd prime set is independent in any set of conflict edges. -/
theorem normal_isIndependent {T : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hT : IsNormalOddPrimeSet T) (hE : ∀ e ∈ E, IsConflictEdge e.1 e.2) :
    IsIndependent E T := by
  intro e he ⟨h1, h2⟩
  have hconf := hE e he
  exact hT.2 e.1 h1 e.2 h2 hconf.1 hconf.2

/-- Splitting a normal odd prime set `P` at cut `p_d` into prefix `S = P.filter (· < p_d)`
and tail `T = P.filter (p_d ≤ ·)`. -/
theorem split_normal_at_cut {P : Finset ℕ} (hP : IsNormalOddPrimeSet P) (p_d : ℕ) :
    let S := P.filter (· < p_d)
    let T := P.filter (p_d ≤ ·)
    IsNormalOddPrimeSet S ∧ IsNormalOddPrimeSet T ∧
      (∀ x ∈ T, IsTailPrime S p_d x) ∧
      Disjoint S T ∧ S ∪ T = P ∧ P.card = S.card + T.card := by
  dsimp only
  set S := P.filter (· < p_d)
  set T := P.filter (p_d ≤ ·)
  have hS_sub : S ⊆ P := Finset.filter_subset _ _
  have hT_sub : T ⊆ P := Finset.filter_subset _ _
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    have h1 : x < p_d := (Finset.mem_filter.mp hxS).2
    have h2 : p_d ≤ x := (Finset.mem_filter.mp hxT).2
    omega
  have hunion : S ∪ T = P := by
    ext x
    simp only [S, T, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases lt_or_ge x p_d with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hcard : P.card = S.card + T.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  refine ⟨hP.subset hS_sub, hP.subset hT_sub, ?_, hdisj, hunion, hcard⟩
  intro x hx
  have hxP : x ∈ P := hT_sub hx
  have hle : p_d ≤ x := (Finset.mem_filter.mp hx).2
  refine ⟨(hP.1 x hxP).1, (hP.1 x hxP).2, hle, ?_⟩
  intro s hs
  have hsP : s ∈ P := hS_sub hs
  have hslt : s < p_d := (Finset.mem_filter.mp hs).2
  exact hP.2 s hsP x hxP (by omega)

/-- When `1 < ∑_{p ∈ P} 1/p`, the tail `T = P.filter (p_d ≤ ·)` satisfies
`need (P.filter (· < p_d)) < ∑_{x ∈ T} 1/x`. -/
theorem need_lt_tail_sum {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) (p_d : ℕ) :
    need (P.filter (· < p_d)) < ∑ x ∈ P.filter (p_d ≤ ·), (1 : ℝ) / (x : ℝ) := by
  have hsplit := split_normal_at_cut hP p_d
  have hdisj := hsplit.2.2.2.1
  have hunion := hsplit.2.2.2.2.1
  have hadd : (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) =
      (∑ s ∈ P.filter (· < p_d), (1 : ℝ) / (s : ℝ)) +
        ∑ x ∈ P.filter (p_d ≤ ·), (1 : ℝ) / (x : ℝ) := by
    conv_lhs => rw [← hunion]
    exact Finset.sum_union hdisj
  unfold need
  linarith

/-! ### Core Edge-Dual Inequality -/

/-- General edge-dual upper bound for any independent subset `A ⊆ U`. -/
theorem edge_dual_le_ub_of_independent {U A : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {w : ℕ → ℝ} {η : ℕ × ℕ → ℝ}
    (hsub : A ⊆ U) (hind : IsIndependent E A) (hη : ∀ e ∈ E, 0 ≤ η e) :
    (∑ x ∈ A, w x) ≤ edgeDualUB U E w η := by
  unfold edgeDualUB
  have hstep1 : ∀ v ∈ A,
      w v ≤ (∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) +
        max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) := by
    intro v _
    linarith [le_max_right (0 : ℝ) (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e)]
  have hsum1 : (∑ v ∈ A, w v) ≤
      (∑ v ∈ A, ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) +
        ∑ v ∈ A, max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hstep1
  have hedge_sum :
      (∑ v ∈ A, ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) ≤ ∑ e ∈ E, η e := by
    have hswap :
        (∑ v ∈ A, ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) =
          ∑ e ∈ E, ∑ v ∈ A.filter (fun v => e.1 = v ∨ e.2 = v), η e := by
      simp_rw [Finset.sum_filter]
      exact Finset.sum_comm
    rw [hswap]
    refine Finset.sum_le_sum fun e he => ?_
    have hcard : (A.filter (fun v => e.1 = v ∨ e.2 = v)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro v₁ hv₁ v₂ hv₂
      have hv₁A : v₁ ∈ A := (Finset.mem_filter.mp hv₁).1
      have hv₂A : v₂ ∈ A := (Finset.mem_filter.mp hv₂).1
      have hv₁e : e.1 = v₁ ∨ e.2 = v₁ := (Finset.mem_filter.mp hv₁).2
      have hv₂e : e.1 = v₂ ∨ e.2 = v₂ := (Finset.mem_filter.mp hv₂).2
      rcases hv₁e with rfl | rfl <;> rcases hv₂e with h2 | h2
      · exact h2
      · exfalso; exact hind e he ⟨hv₁A, h2 ▸ hv₂A⟩
      · exfalso; exact hind e he ⟨h2 ▸ hv₂A, hv₁A⟩
      · exact h2
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcardR : ((A.filter (fun v => e.1 = v ∨ e.2 = v)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    nlinarith [hη e he]
  have hmax_sum :
      (∑ v ∈ A, max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e)) ≤
        ∑ v ∈ U, max 0 (w v - ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro v _ _
    exact le_max_left 0 _
  linarith

/-- **Core Edge-Dual Inequality**: if every edge `e ∈ E` is a conflict edge between vertices
in `U`, `∀ e ∈ E, 0 ≤ η e`, and `T` is a normal odd prime set, then
`∑ x ∈ T ∩ U, w x ≤ edgeDualUB U E w η`. -/
theorem edge_dual_le_ub {U T : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {w : ℕ → ℝ} {η : ℕ × ℕ → ℝ}
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) (hT : IsNormalOddPrimeSet T) :
    (∑ x ∈ T ∩ U, w x) ≤ edgeDualUB U E w η := by
  have hind : IsIndependent E (T ∩ U) :=
    normal_isIndependent (hT.subset Finset.inter_subset_left) (fun e he => (hE e he).2.2)
  exact edge_dual_le_ub_of_independent Finset.inter_subset_right hind hη

/-- Helper: splitting `∑_{x ∈ T} w x ≤ ∑_{x ∈ T ∩ V} w x` when `w x ≤ 0` outside `V`. -/
lemma sum_le_sum_inter_of_nonpos {T V : Finset ℕ} {w : ℕ → ℝ}
    (hnonpos : ∀ x ∈ T, x ∉ V → w x ≤ 0) :
    (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ V, w x := by
  have hdisj : Disjoint (T ∩ V) (T \ V) :=
    Finset.disjoint_left.mpr fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have hunion : (T ∩ V) ∪ (T \ V) = T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hpart : (∑ x ∈ T, w x) = (∑ x ∈ T ∩ V, w x) + ∑ x ∈ T \ V, w x := by
    conv_lhs => rw [← hunion]
    exact Finset.sum_union hdisj
  have hsdiff : (∑ x ∈ T \ V, w x) ≤ 0 := by
    refine Finset.sum_nonpos fun x hx => ?_
    rw [Finset.mem_sdiff] at hx
    exact hnonpos x hx.1 hx.2
  linarith

/-! ### Lemma W — Forest Forms (F1) and (F2) -/

/-- **Lemma W, Form (F1) (Forest Count Bound)**:
For any spanning subgraph `(V, E_F)` of the conflict graph on tail primes up to `X`
(so every tail prime `x ≤ X` lies in `V` and every edge in `E_F` is a conflict edge in `V`),
and any `lam ≥ 1 / X` (with `0 < X`),
`(T.card : ℝ) > (need S - mwis V E_F (fun x => 1 / x - lam)) / lam`. -/
theorem lemma_w_forest_count {S T V : Finset ℕ} {E_F : Finset (ℕ × ℕ)}
    {p_d X : ℕ} {lam : ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hX : 0 < X)
    (hV : ∀ x, IsTailPrime S p_d x → x ≤ X → x ∈ V)
    (hE : ∀ e ∈ E_F, e.1 ∈ V ∧ e.2 ∈ V ∧ IsConflictEdge e.1 e.2)
    (hlam : (1 : ℝ) / (X : ℝ) ≤ lam) :
    (need S - mwis V E_F (fun x => (1 : ℝ) / (x : ℝ) - lam)) / lam < (T.card : ℝ) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX
  have hlam_pos : 0 < lam := lt_of_lt_of_le (div_pos one_pos hXpos) hlam
  let w : ℕ → ℝ := fun x => (1 : ℝ) / (x : ℝ) - lam
  have hnonpos : ∀ x ∈ T, x ∉ V → w x ≤ 0 := by
    intro x hx hxV
    have hxt := hTail x hx
    have hgt : X < x := by
      by_contra hle
      exact hxV (hV x hxt (Nat.not_lt.mp hle))
    have hgtR : (X : ℝ) < (x : ℝ) := Nat.cast_lt.mpr hgt
    have hinv : (1 : ℝ) / (x : ℝ) ≤ (1 : ℝ) / (X : ℝ) :=
      one_div_le_one_div_of_le hXpos (le_of_lt hgtR)
    dsimp only [w]
    linarith
  have h1 : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ V, w x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ V, w x) ≤ mwis V E_F w :=
    le_mwis Finset.inter_subset_right
      (normal_isIndependent (hT.subset Finset.inter_subset_left) (fun e he => (hE e he).2.2))
  have hsum : (∑ x ∈ T, w x) = (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - lam * (T.card : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have h3 : need S - lam * (T.card : ℝ) < mwis V E_F w := by linarith
  rw [div_lt_iff₀ hlam_pos]
  linarith

/-- **Lemma W, Form (F2) (Forest Product / Log Bound)**:
For any spanning subgraph `(V, E_F)` of the conflict graph on tail primes up to `X ≥ 1`
and any `0 < μ ≤ X * Real.log X`,
`μ * need S - mwis V E_F (fun x => μ / x - Real.log x) < ∑ x ∈ T, Real.log x`. -/
theorem lemma_w_forest_prod {S T V : Finset ℕ} {E_F : Finset (ℕ × ℕ)}
    {p_d X : ℕ} {μ : ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hX : 1 ≤ X)
    (hV : ∀ x, IsTailPrime S p_d x → x ≤ X → x ∈ V)
    (hE : ∀ e ∈ E_F, e.1 ∈ V ∧ e.2 ∈ V ∧ IsConflictEdge e.1 e.2)
    (hμ0 : 0 < μ)
    (hμ : μ ≤ (X : ℝ) * Real.log (X : ℝ)) :
    μ * need S - mwis V E_F (fun x => μ / (x : ℝ) - Real.log (x : ℝ)) <
      ∑ x ∈ T, Real.log (x : ℝ) := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le zero_lt_one hX1
  let w : ℕ → ℝ := fun x => μ / (x : ℝ) - Real.log (x : ℝ)
  have hnonpos : ∀ x ∈ T, x ∉ V → w x ≤ 0 := by
    intro x hx hxV
    have hxt := hTail x hx
    have hgt : X < x := by
      by_contra hle
      exact hxV (hV x hxt (Nat.not_lt.mp hle))
    have hgtR : (X : ℝ) < (x : ℝ) := Nat.cast_lt.mpr hgt
    have hxpos : (0 : ℝ) < (x : ℝ) := lt_trans hXpos hgtR
    have hlog_nonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
    have hlog_le : Real.log (X : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log hXpos (le_of_lt hgtR)
    have hmul : (X : ℝ) * Real.log (X : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) :=
      mul_le_mul (le_of_lt hgtR) hlog_le hlog_nonneg (le_of_lt hxpos)
    have hdiv : μ / (x : ℝ) ≤ Real.log (x : ℝ) :=
      (div_le_iff₀ hxpos).mpr (by linarith)
    dsimp only [w]
    linarith
  have h1 : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ V, w x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ V, w x) ≤ mwis V E_F w :=
    le_mwis Finset.inter_subset_right
      (normal_isIndependent (hT.subset Finset.inter_subset_left) (fun e he => (hE e he).2.2))
  have hsum : (∑ x ∈ T, w x) =
      μ * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - ∑ x ∈ T, Real.log (x : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, div_eq_mul_inv, one_mul, ← Finset.mul_sum]
  have hmul_lt : μ * need S < μ * ∑ x ∈ T, (1 : ℝ) / (x : ℝ) :=
    mul_lt_mul_of_pos_left hneed hμ0
  linarith

/-! ### Lemma W — Edge-Dual Forms (E) -/

/-- **Lemma W, Form (E) (Edge-Dual Count Bound)**:
For any cutoff `Λ > 0`, vertex set `U` holding every tail prime strictly below `Λ`,
conflict edge set `E` on `U`, and nonnegative dual weights `η ≥ 0`:
`Λ * (need S - edgeDualUB U E (fun x => 1 / x - 1 / Λ) η) < (T.card : ℝ)`. -/
theorem lemma_w_edge_dual_count {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d : ℕ} {Λ : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hΛ : 0 < Λ)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < Λ → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    Λ * (need S - edgeDualUB U E (fun x => (1 : ℝ) / (x : ℝ) - 1 / Λ) η) < (T.card : ℝ) := by
  let w : ℕ → ℝ := fun x => (1 : ℝ) / (x : ℝ) - 1 / Λ
  have hnonpos : ∀ x ∈ T, x ∉ U → w x ≤ 0 := by
    intro x hx hxU
    have hle : Λ ≤ (x : ℝ) := by
      by_contra hlt
      exact hxU (hU x (hTail x hx) (lt_of_not_ge hlt))
    have hinv : (1 : ℝ) / (x : ℝ) ≤ 1 / Λ := one_div_le_one_div_of_le hΛ hle
    dsimp only [w]
    linarith
  have h1 : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ U, w x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ U, w x) ≤ edgeDualUB U E w η := edge_dual_le_ub hE hη hT
  have hsum : (∑ x ∈ T, w x) = (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - (T.card : ℝ) / Λ := by
    simp only [w, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h3 : need S - (T.card : ℝ) / Λ < edgeDualUB U E w η := by linarith
  have h4 : need S - edgeDualUB U E w η < (T.card : ℝ) / Λ := by linarith
  have h5 := mul_lt_mul_of_pos_left h4 hΛ
  have hcancel : Λ * ((T.card : ℝ) / Λ) = (T.card : ℝ) := by field_simp [ne_of_gt hΛ]
  rwa [hcancel] at h5

/-- **Lemma W, Form (E) (Edge-Dual Product / Log Bound)**:
For `1 ≤ Λ`, `0 < μ ≤ Λ * Real.log Λ`, `U` holding every tail prime below `Λ`,
conflict edges `E` on `U`, and `η ≥ 0`:
`μ * need S - edgeDualUB U E (fun x => μ / x - Real.log x) η < ∑ x ∈ T, Real.log x`. -/
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
      ∑ x ∈ T, Real.log (x : ℝ) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let w : ℕ → ℝ := fun x => μ / (x : ℝ) - Real.log (x : ℝ)
  have hnonpos : ∀ x ∈ T, x ∉ U → w x ≤ 0 := by
    intro x hx hxU
    have hle : Λ ≤ (x : ℝ) := by
      by_contra hlt
      exact hxU (hU x (hTail x hx) (lt_of_not_ge hlt))
    have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le hΛpos hle
    have hlog_nonneg : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
    have hlog_le : Real.log Λ ≤ Real.log (x : ℝ) := Real.log_le_log hΛpos hle
    have hmul : Λ * Real.log Λ ≤ (x : ℝ) * Real.log (x : ℝ) :=
      mul_le_mul hle hlog_le hlog_nonneg (le_of_lt hxpos)
    have hdiv : μ / (x : ℝ) ≤ Real.log (x : ℝ) :=
      (div_le_iff₀ hxpos).mpr (by linarith)
    dsimp only [w]
    linarith
  have h1 : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ U, w x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ U, w x) ≤ edgeDualUB U E w η := edge_dual_le_ub hE hη hT
  have hsum : (∑ x ∈ T, w x) =
      μ * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - ∑ x ∈ T, Real.log (x : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, div_eq_mul_inv, one_mul, ← Finset.mul_sum]
  have hmul_lt : μ * need S < μ * ∑ x ∈ T, (1 : ℝ) / (x : ℝ) :=
    mul_lt_mul_of_pos_left hneed hμ0
  linarith

/-! ### Complete Frontier Theorem -/

/-- Every normal odd prime set `P` hits the unique leaf `S = P.filter (· < p_d)` in any
complete frontier `F` below `p_d`. -/
theorem exists_unique_leaf_in_frontier {p_d : ℕ} {F : Finset (Finset ℕ)}
    (hF : ∀ S : Finset ℕ, IsNormalOddPrimeSet S → (∀ s ∈ S, s < p_d) → S ∈ F)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P) :
    ∃! S ∈ F, S = P.filter (· < p_d) := by
  refine ⟨P.filter (· < p_d), ⟨?_, rfl⟩, fun _ h => h.2⟩
  exact hF _ (hP.subset (Finset.filter_subset _ _)) (fun s hs => (Finset.mem_filter.mp hs).2)

/-- **Complete Frontier Theorem**: over a complete frontier `F` of normal odd prime sets
below `p_d`, if each leaf `S ∈ F` carries a valid Lemma W Form (E) certificate certifying
`B S` tail primes (via `(B S : ℝ) - 1 ≤ Λ S * (need S - edgeDualUB ...)`), then every
normal odd prime set `P` with `∑ 1/p > 1` satisfies `min_{S ∈ F} (|S| + B S) ≤ |P|`. -/
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
    F.inf' ⟨∅, hF ∅ ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩ (fun _ h => by simp at h)⟩
        (fun S => S.card + B S) ≤ P.card := by
  set S := P.filter (· < p_d)
  set T := P.filter (p_d ≤ ·)
  have hsplit := split_normal_at_cut hP p_d
  have hS_mem : S ∈ F :=
    hF S hsplit.1 (fun s hs => (Finset.mem_filter.mp hs).2)
  have hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ) := need_lt_tail_sum hP hsum p_d
  have hbound := lemma_w_edge_dual_count hsplit.2.1 hsplit.2.2.1 hneed
    (hΛ S hS_mem) (hU S hS_mem) (hE S hS_mem) (hη S hS_mem)
  have hBS_lt : (B S : ℝ) - 1 < (T.card : ℝ) := lt_of_le_of_lt (hB S hS_mem) hbound
  have hBS_le : B S ≤ T.card := by
    by_cases h0 : B S = 0
    · omega
    · have hcast : ((B S - 1 : ℕ) : ℝ) < (T.card : ℝ) := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h0), Nat.cast_one]
        exact hBS_lt
      have hlt : B S - 1 < T.card := Nat.cast_lt.mp hcast
      omega
  have hinf_le :
      F.inf' ⟨∅, hF ∅ ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩ (fun _ h => by simp at h)⟩
        (fun L => L.card + B L) ≤ S.card + B S :=
    Finset.inf'_le _ hS_mem
  have hcard : P.card = S.card + T.card := hsplit.2.2.2.2.2
  omega

/-! ### Lemma W — Refinement 1 (`Λ / v - 1` weights and exact scaling) -/

/-- **Lemma W, Refinement 1 (`lemma-w-2.md`)**:
With scaled count weights `w_v = Λ / v - 1` on `U` (`Λ > 0`),
`(T.card : ℝ) > Λ * need S - edgeDualUB U E (fun x => Λ / x - 1) η`. -/
theorem lemma_w_refinement1 {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d : ℕ} {Λ : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hΛ : 0 < Λ)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < Λ → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    Λ * need S - edgeDualUB U E (fun x => Λ / (x : ℝ) - 1) η < (T.card : ℝ) := by
  let w : ℕ → ℝ := fun x => Λ / (x : ℝ) - 1
  have hnonpos : ∀ x ∈ T, x ∉ U → w x ≤ 0 := by
    intro x hx hxU
    have hle : Λ ≤ (x : ℝ) := by
      by_contra hlt
      exact hxU (hU x (hTail x hx) (lt_of_not_ge hlt))
    have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le hΛ hle
    have hdiv : Λ / (x : ℝ) ≤ 1 := (div_le_one hxpos).mpr hle
    dsimp only [w]
    linarith
  have h1 : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ U, w x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ U, w x) ≤ edgeDualUB U E w η := edge_dual_le_ub hE hη hT
  have hsum : (∑ x ∈ T, w x) = Λ * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - (T.card : ℝ) := by
    simp only [w, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      div_eq_mul_inv, one_mul, ← Finset.mul_sum]
  have hmul_lt : Λ * need S < Λ * ∑ x ∈ T, (1 : ℝ) / (x : ℝ) :=
    mul_lt_mul_of_pos_left hneed hΛ
  linarith

/-- **Refinement 1 Exact Scaling Identity**:
With `η_e = Λ * μ_e` (`Λ > 0`), `edgeDualUB U E (Λ/v - 1) (Λ * μ) = Λ * edgeDualUB U E (1/v - 1/Λ) μ`. -/
theorem lemma_w_refinement1_scaling (U : Finset ℕ) (E : Finset (ℕ × ℕ))
    {Λ : ℝ} (hΛ : 0 < Λ) (μ : ℕ × ℕ → ℝ) :
    edgeDualUB U E (fun x => Λ / (x : ℝ) - 1) (fun e => Λ * μ e) =
      Λ * edgeDualUB U E (fun x => (1 : ℝ) / (x : ℝ) - 1 / Λ) μ := by
  unfold edgeDualUB
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [mul_max_of_nonneg _ _ (le_of_lt hΛ), mul_zero]
  congr 1
  rw [← Finset.mul_sum]
  have hΛ0 : Λ ≠ 0 := ne_of_gt hΛ
  field_simp [hΛ0]

/-! ### Lemma W — Refinement 2 (`μ / x + ν - ln x` size bound) -/

/-- Helper: `f(x) = μ / x + ν - Real.log x` is antitone on `(0, ∞)` when `0 ≤ μ`,
so `f(C) ≤ 0` (`C > 0`) implies `f(x) ≤ 0` for all `x ≥ C`. -/
lemma refinement2_weight_nonpos {μ ν C x : ℝ} (hμ : 0 ≤ μ) (hC : 0 < C)
    (hfC : μ / C + ν - Real.log C ≤ 0) (hle : C ≤ x) :
    μ / x + ν - Real.log x ≤ 0 := by
  have hdiv : μ / x ≤ μ / C := div_le_div_of_nonneg_left hμ hC hle
  have hlog : Real.log C ≤ Real.log x := Real.log_le_log hC hle
  linarith

/-- **Lemma W, Refinement 2 (`lemma-w-2.md`, exact `≥` form)**:
For `K ≤ T.card`, `0 ≤ μ`, `0 ≤ ν`, `C > 0`, `μ / C + ν - Real.log C ≤ 0`,
`U` holding every tail prime below `C`, conflict edges `E` on `U`, and `η ≥ 0`:
`μ * need S + ν * K - edgeDualUB U E (fun x => μ / x + ν - Real.log x) η ≤ ∑ x ∈ T, Real.log x`. -/
theorem lemma_w_refinement2 {S T U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    {p_d K : ℕ} {μ ν C : ℝ} {η : ℕ × ℕ → ℝ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S p_d x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hK : K ≤ T.card)
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hC : 0 < C)
    (hfC : μ / C + ν - Real.log C ≤ 0)
    (hU : ∀ x, IsTailPrime S p_d x → (x : ℝ) < C → x ∈ U)
    (hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2)
    (hη : ∀ e ∈ E, 0 ≤ η e) :
    μ * need S + ν * (K : ℝ) -
        edgeDualUB U E (fun x => μ / (x : ℝ) + ν - Real.log (x : ℝ)) η ≤
      ∑ x ∈ T, Real.log (x : ℝ) := by
  let f : ℕ → ℝ := fun x => μ / (x : ℝ) + ν - Real.log (x : ℝ)
  have hnonpos : ∀ x ∈ T, x ∉ U → f x ≤ 0 := by
    intro x hx hxU
    have hle : C ≤ (x : ℝ) := by
      by_contra hlt
      exact hxU (hU x (hTail x hx) (lt_of_not_ge hlt))
    exact refinement2_weight_nonpos hμ hC hfC hle
  have h1 : (∑ x ∈ T, f x) ≤ ∑ x ∈ T ∩ U, f x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ U, f x) ≤ edgeDualUB U E f η := edge_dual_le_ub hE hη hT
  have hsum : (∑ x ∈ T, f x) =
      μ * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) + ν * (T.card : ℝ) - ∑ x ∈ T, Real.log (x : ℝ) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv, one_mul, ← Finset.mul_sum]
    ring
  have hμ_le : μ * need S ≤ μ * ∑ x ∈ T, (1 : ℝ) / (x : ℝ) :=
    mul_le_mul_of_nonneg_left (le_of_lt hneed) hμ
  have hKR : (K : ℝ) ≤ (T.card : ℝ) := Nat.cast_le.mpr hK
  have hν_le : ν * (K : ℝ) ≤ ν * (T.card : ℝ) := mul_le_mul_of_nonneg_left hKR hν
  linarith

/-- **Lemma W, Refinement 2 (`lemma-w-2.md`, strict `>` form when `μ > 0`)**:
Under the same hypotheses as `lemma_w_refinement2` with `0 < μ`:
`μ * need S + ν * K - edgeDualUB U E (fun x => μ / x + ν - Real.log x) η < ∑ x ∈ T, Real.log x`. -/
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
      ∑ x ∈ T, Real.log (x : ℝ) := by
  let f : ℕ → ℝ := fun x => μ / (x : ℝ) + ν - Real.log (x : ℝ)
  have hnonpos : ∀ x ∈ T, x ∉ U → f x ≤ 0 := by
    intro x hx hxU
    have hle : C ≤ (x : ℝ) := by
      by_contra hlt
      exact hxU (hU x (hTail x hx) (lt_of_not_ge hlt))
    exact refinement2_weight_nonpos (le_of_lt hμ) hC hfC hle
  have h1 : (∑ x ∈ T, f x) ≤ ∑ x ∈ T ∩ U, f x := sum_le_sum_inter_of_nonpos hnonpos
  have h2 : (∑ x ∈ T ∩ U, f x) ≤ edgeDualUB U E f η := edge_dual_le_ub hE hη hT
  have hsum : (∑ x ∈ T, f x) =
      μ * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) + ν * (T.card : ℝ) - ∑ x ∈ T, Real.log (x : ℝ) := by
    simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv, one_mul, ← Finset.mul_sum]
    ring
  have hμ_lt : μ * need S < μ * ∑ x ∈ T, (1 : ℝ) / (x : ℝ) :=
    mul_lt_mul_of_pos_left hneed hμ
  have hKR : (K : ℝ) ≤ (T.card : ℝ) := Nat.cast_le.mpr hK
  have hν_le : ν * (K : ℝ) ≤ ν * (T.card : ℝ) := mul_le_mul_of_nonneg_left hKR hν
  linarith

/-! ### Unconditional Hand Case (`|P| ≥ 9`) -/

/-- **Unconditional Hand Case (`lemma-w-1.md`, BBBG `i₁ = 9`)**:
Using Lemma W Form (E) with `S = ∅`, `Λ = 13`, `U = {3, 5, 7, 11}`, edges `{(3, 7), (5, 11)}`,
and dual weights `η(3, 7) = 6/91`, `η(5, 11) = 2/143`, every normal odd prime set `P`
with `∑_{p ∈ P} 1/p > 1` has at least `9` elements (`|P| > 121/15 = 8.066…`). -/
theorem hand_case_nine_primes {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    9 ≤ P.card := by
  let U : Finset ℕ := {3, 5, 7, 11}
  let E : Finset (ℕ × ℕ) := {(3, 7), (5, 11)}
  let η : ℕ × ℕ → ℝ := fun e =>
    if e = (3, 7) then (6 : ℝ) / 91 else if e = (5, 11) then (2 : ℝ) / 143 else 0
  have hTail : ∀ x ∈ P, IsTailPrime ∅ 3 x := by
    intro x hx
    obtain ⟨hpr, hodd⟩ := hP.1 x hx
    have hge3 : 3 ≤ x := by
      have h2 := hpr.two_le
      rcases hodd with ⟨k, rfl⟩
      omega
    exact ⟨hpr, hodd, hge3, fun s hs => by simp at hs⟩
  have hneed : need ∅ < ∑ x ∈ P, (1 : ℝ) / (x : ℝ) := by
    simpa [need] using hsum
  have hU : ∀ x, IsTailPrime ∅ 3 x → (x : ℝ) < 13 → x ∈ U := by
    intro x ⟨hpr, _, hge3, _⟩ hlt
    have hx_lt : x < 13 := by exact_mod_cast hlt
    interval_cases x
    all_goals first | decide | (exfalso; norm_num at hpr)
  have hE : ∀ e ∈ E, e.1 ∈ U ∧ e.2 ∈ U ∧ IsConflictEdge e.1 e.2 := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · refine ⟨by decide, by decide, by decide, by decide⟩
    · refine ⟨by decide, by decide, by decide, by decide⟩
  have hη : ∀ e ∈ E, 0 ≤ η e := by
    intro e he
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [η] <;> norm_num
  have hbound := lemma_w_edge_dual_count (S := ∅) (T := P) (U := U) (E := E) (p_d := 3)
    (Λ := 13) (η := η) hP hTail hneed (by norm_num) hU hE hη
  have hUB : edgeDualUB U E (fun x => (1 : ℝ) / (x : ℝ) - 1 / 13) η = 74 / 195 := by
    unfold edgeDualUB
    have hE_sum : (∑ e ∈ E, η e) = 6 / 91 + 2 / 143 := by
      simp [E, η]
    have hf3 : E.filter (fun e => e.1 = 3 ∨ e.2 = 3) = {(3, 7)} := by decide
    have hf5 : E.filter (fun e => e.1 = 5 ∨ e.2 = 5) = {(5, 11)} := by decide
    have hf7 : E.filter (fun e => e.1 = 7 ∨ e.2 = 7) = {(3, 7)} := by decide
    have hf11 : E.filter (fun e => e.1 = 11 ∨ e.2 = 11) = {(5, 11)} := by decide
    have hU_sum :
        (∑ v ∈ U, max (0 : ℝ) ((1 : ℝ) / (v : ℝ) - 1 / 13 -
          ∑ e ∈ E.filter (fun e => e.1 = v ∨ e.2 = v), η e)) =
        max (0 : ℝ) ((1 : ℝ) / 3 - 1 / 13 - (6 : ℝ) / 91) +
        max (0 : ℝ) ((1 : ℝ) / 5 - 1 / 13 - (2 : ℝ) / 143) +
        max (0 : ℝ) ((1 : ℝ) / 7 - 1 / 13 - (6 : ℝ) / 91) +
        max (0 : ℝ) ((1 : ℝ) / 11 - 1 / 13 - (2 : ℝ) / 143) := by
      have h1 : (3 : ℕ) ∉ ({5, 7, 11} : Finset ℕ) := by decide
      have h2 : (5 : ℕ) ∉ ({7, 11} : Finset ℕ) := by decide
      have h3 : (7 : ℕ) ∉ ({11} : Finset ℕ) := by decide
      simp only [U, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
        Finset.sum_singleton, hf3, hf5, hf7, hf11, η]
      norm_num
    rw [hE_sum, hU_sum]
    norm_num
  have hneed0 : need ∅ = 1 := by simp [need]
  rw [hUB, hneed0] at hbound
  have h8 : (8 : ℝ) < (P.card : ℝ) := by linarith
  have h8N : 8 < P.card := by exact_mod_cast h8
  omega

/-- Immediate unconditional corollary: every Giuga counterexample has at least `9` prime factors. -/
theorem giuga_nine_primes {n : ℕ} (hn : IsGiugaCounterexample n) :
    9 ≤ n.primeFactors.card :=
  hand_case_nine_primes (giuga_primeFactors_normal hn) (giuga_recip_sum_gt_one hn)

end Giuga
