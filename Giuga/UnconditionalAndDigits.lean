module

public import Giuga.Defs
public import Giuga.LemmaW
public import Giuga.CeilingAndRules

import Mathlib.Tactic

/-!
# Unconditional Mod-8 Rule, 578-Prime Pure-Kernel Bound, and Explicit Digit Corollaries

Strengthens `lean/Giuga` in three directions (zero `sorry`, zero `native_decide`,
standard axioms only):
1. **Mavrotheris's Modulo-8 Count Congruence** (`giuga_card_mod_eight`):
   `n.primeFactors.card ≡ v + 1 [MOD 8]` for every Giuga counterexample `n` of value `v`,
   derived elementarily from `giuga_reciprocity_rule` and `giuga_residue_mod_8`.
2. **Stronger Unconditional Pure-Kernel Lower Bounds** (`unconditional_normal_set_575`,
   `giuga_unconditional_578_primes`, `giuga_unconditional_gt_10_pow_1803`):
   a compact 2-leaf (`d = 2`, `p₂ = 5`, `Λ = 3000`) scaled-integer Lemma W certificate
   replayed in `< 0.5 s` via a verified binary radix trie (`Trie`) and GMP bitmask,
   proving unconditionally (without `hN1`) that every normal odd prime set with
   `∑ 1/p > 1` has `≥ 575` primes and every Giuga counterexample has `≥ 578` prime factors
   and `n > 10 ^ 1803` (`≥ 1,804` decimal digits), surpassing Giuga (1950) and
   Bedocchi (1985) purely inside the Lean 4 kernel.
3. **Explicit Decimal-Digit Corollaries** (`cor_giuga_gt_10_pow_36083`,
   `lemma_C_prod_gt_10_pow_446177`, `lemma_w_refinement2_route_a`,
   `cor_giuga_route_a_gt_10_pow_40747`):
   - From `hN1` alone (zero log-certificate hypotheses): `10 ^ 36083 < n` for every
     Giuga counterexample `n` (surpassing BBBG Open Problem 5's `10 ^ 36068`), and
     `10 ^ 446177 < ∏ p ∈ P, p` for `∑ 1/p > 2`.
   - Route (a) K7-linear-lift theorem (`lemma_w_refinement2_route_a`) and instantiated
     digit bound `10 ^ 40747 < n` (`≥ 40,748` decimal digits).
-/

@[expose] public section

namespace Giuga

open scoped BigOperators

/-! ### Part 1: Elementary Pure-Kernel Proof of `m ≡ v + 1 [MOD 8]` -/

/-- Helper: in `ZMod 8`, `4 * x = 4` for every odd natural number `x`. -/
lemma odd_four_mul_zmod8 {x : ℕ} (hx : Odd x) : (4 : ZMod 8) * (x : ZMod 8) = 4 := by
  rcases hx with ⟨t, rfl⟩
  push_cast
  have h : (4 : ZMod 8) * (2 * (t : ZMod 8) + 1) = (8 : ZMod 8) * (t : ZMod 8) + 4 := by ring
  rw [h]
  change (0 : ZMod 8) * (t : ZMod 8) + 4 = 4
  simp

/-- Helper: for any finite set `Q` of odd naturals, `∏ p ∈ Q, p` is odd. -/
lemma odd_prod_of_forall_odd {Q : Finset ℕ} (hQ : ∀ p ∈ Q, Odd p) :
    Odd (∏ p ∈ Q, p) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    exact (hQ p (Finset.mem_insert_self p s)).mul
      (ih (fun q hq => hQ q (Finset.mem_insert_of_mem hq)))

/-- Helper: in `ZMod 8`, `2 * ∏_{p ∈ Q} p = 2 + 4 * #{p ∈ Q : p % 4 = 3}` for odd naturals. -/
lemma two_mul_prod_odd_zmod8 {Q : Finset ℕ} (hQ : ∀ p ∈ Q, Odd p) :
    (2 : ZMod 8) * (∏ p ∈ Q, (p : ZMod 8)) =
      2 + 4 * ((Q.filter (fun p => p % 4 = 3)).card : ZMod 8) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp : Odd p := hQ p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, Odd q := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hps, ← mul_assoc, mul_comm (2 : ZMod 8) (p : ZMod 8), mul_assoc,
      ih hs]
    set k := (s.filter (fun q => q % 4 = 3)).card
    have hrem : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      rcases hp with ⟨t, rfl⟩; omega
    rcases hrem with h1 | h3 | h5 | h7
    · have hp4 : ¬ (p % 4 = 3) := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) = s.filter (fun q => q % 4 = 3) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hpz : (p : ZMod 8) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
      rw [hfilt, hpz, one_mul]
    · have hp4 : p % 4 = 3 := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) =
          insert p (s.filter (fun q => q % 4 = 3)) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hp_not_mem : p ∉ s.filter (fun q => q % 4 = 3) := fun hm =>
        hps (Finset.mem_filter.mp hm).1
      rw [hfilt, Finset.card_insert_of_notMem hp_not_mem, Nat.cast_add, Nat.cast_one]
      have hpz : (p : ZMod 8) = 3 := by rw [← ZMod.natCast_mod, h3]; rfl
      rw [hpz]
      have h8 : (3 : ZMod 8) * (2 + 4 * (k : ZMod 8)) - (2 + 4 * ((k : ZMod 8) + 1)) =
          (8 : ZMod 8) * (k : ZMod 8) := by ring
      have hz : (8 : ZMod 8) * (k : ZMod 8) = 0 := by
        change (0 : ZMod 8) * (k : ZMod 8) = 0; simp
      rw [hz] at h8
      exact sub_eq_zero.mp h8
    · have hp4 : ¬ (p % 4 = 3) := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) = s.filter (fun q => q % 4 = 3) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hpz : (p : ZMod 8) = 5 := by rw [← ZMod.natCast_mod, h5]; rfl
      rw [hfilt, hpz]
      have h8 : (5 : ZMod 8) * (2 + 4 * (k : ZMod 8)) - (2 + 4 * (k : ZMod 8)) =
          (8 : ZMod 8) * (1 + 2 * (k : ZMod 8)) := by ring
      have hz : (8 : ZMod 8) * (1 + 2 * (k : ZMod 8)) = 0 := by
        change (0 : ZMod 8) * _ = 0; simp
      rw [hz] at h8
      exact sub_eq_zero.mp h8
    · have hp4 : p % 4 = 3 := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) =
          insert p (s.filter (fun q => q % 4 = 3)) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hp_not_mem : p ∉ s.filter (fun q => q % 4 = 3) := fun hm =>
        hps (Finset.mem_filter.mp hm).1
      rw [hfilt, Finset.card_insert_of_notMem hp_not_mem, Nat.cast_add, Nat.cast_one]
      have hpz : (p : ZMod 8) = 7 := by rw [← ZMod.natCast_mod, h7]; rfl
      rw [hpz]
      have h8 : (7 : ZMod 8) * (2 + 4 * (k : ZMod 8)) - (2 + 4 * ((k : ZMod 8) + 1)) =
          (8 : ZMod 8) * (1 + 3 * (k : ZMod 8)) := by ring
      have hz : (8 : ZMod 8) * (1 + 3 * (k : ZMod 8)) = 0 := by
        change (0 : ZMod 8) * _ = 0; simp
      rw [hz] at h8
      exact sub_eq_zero.mp h8

/-- Helper: `(k + 1) * k / 2 = k * (k - 1) / 2 + k` for all `k : ℕ`. -/
lemma choose_two_succ (k : ℕ) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  rcases k with _ | m
  · simp
  · have hev : 2 ∣ (m + 1) * m := even_iff_two_dvd.mp (Nat.even_mul_pred_self (m + 1))
    rcases hev with ⟨t, ht⟩
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub, ht]
    have h2 : (m + 2) * (m + 1) = 2 * (t + (m + 1)) := by linarith
    rw [h2, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]

/-- Universal mod-8 identity for finite sets of odd naturals (`Remark 6`):
`(∑ p ∈ Q, p) - (∏ p ∈ Q, p) = |Q| - 1 - 4 * C(k₃, 2)` in `ZMod 8`. -/
theorem sum_sub_prod_odd_zmod8 {Q : Finset ℕ} (hQ : ∀ p ∈ Q, Odd p) :
    (∑ p ∈ Q, (p : ZMod 8)) - (∏ p ∈ Q, (p : ZMod 8)) =
      (Q.card : ZMod 8) - 1 -
        4 * ((((Q.filter (fun p => p % 4 = 3)).card *
          ((Q.filter (fun p => p % 4 = 3)).card - 1) / 2 : ℕ) : ZMod 8)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp : Odd p := hQ p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, Odd q := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    rw [Finset.sum_insert hps, Finset.prod_insert hps, Finset.card_insert_of_notMem hps,
      Nat.cast_add, Nat.cast_one]
    set S := ∑ q ∈ s, (q : ZMod 8)
    set P := ∏ q ∈ s, (q : ZMod 8)
    set k := (s.filter (fun q => q % 4 = 3)).card
    have hP_odd : Odd (∏ q ∈ s, q) := odd_prod_of_forall_odd hs
    have h4P : (4 : ZMod 8) * P = 4 := by
      have := odd_four_mul_zmod8 hP_odd
      simpa [P, Nat.cast_prod] using this
    have h2P : (2 : ZMod 8) * P = 2 + 4 * (k : ZMod 8) := two_mul_prod_odd_zmod8 hs
    have hrem : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
      rcases hp with ⟨t, rfl⟩; omega
    rcases hrem with h1 | h3 | h5 | h7
    · have hp4 : ¬ (p % 4 = 3) := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) = s.filter (fun q => q % 4 = 3) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hpz : (p : ZMod 8) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
      rw [hfilt, hpz]
      linear_combination ih hs
    · have hp4 : p % 4 = 3 := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) =
          insert p (s.filter (fun q => q % 4 = 3)) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hp_not_mem : p ∉ s.filter (fun q => q % 4 = 3) := fun hm =>
        hps (Finset.mem_filter.mp hm).1
      rw [hfilt, Finset.card_insert_of_notMem hp_not_mem]
      have hch : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
        simpa using choose_two_succ k
      rw [hch, Nat.cast_add]
      have hpz : (p : ZMod 8) = 3 := by rw [← ZMod.natCast_mod, h3]; rfl
      rw [hpz]
      linear_combination (ih hs) - h2P
    · have hp4 : ¬ (p % 4 = 3) := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) = s.filter (fun q => q % 4 = 3) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hpz : (p : ZMod 8) = 5 := by rw [← ZMod.natCast_mod, h5]; rfl
      rw [hfilt, hpz]
      linear_combination (ih hs) - h4P
    · have hp4 : p % 4 = 3 := by omega
      have hfilt : (insert p s).filter (fun q => q % 4 = 3) =
          insert p (s.filter (fun q => q % 4 = 3)) := by
        simp only [Finset.filter_insert, hp4, ↓reduceIte]
      have hp_not_mem : p ∉ s.filter (fun q => q % 4 = 3) := fun hm =>
        hps (Finset.mem_filter.mp hm).1
      rw [hfilt, Finset.card_insert_of_notMem hp_not_mem]
      have hch : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
        simpa using choose_two_succ k
      rw [hch, Nat.cast_add]
      have hpz : (p : ZMod 8) = 7 := by rw [← ZMod.natCast_mod, h7]; rfl
      rw [hpz]
      linear_combination (ih hs) - h4P - h2P

/-- **Mavrotheris's Modulo-8 Count Congruence (Unconditional Pure-Kernel Proof)**:
For every Giuga counterexample `n` with value `v` (`∑ p ∈ n.primeFactors, n / p = v * n + 1`),
`n.primeFactors.card ≡ v + 1 [MOD 8]`. -/
theorem giuga_card_mod_eight {n v : ℕ} (hn : IsGiugaCounterexample n)
    (hv : ∑ p ∈ n.primeFactors, n / p = v * n + 1) :
    n.primeFactors.card ≡ v + 1 [MOD 8] := by
  set P := n.primeFactors
  have hodd : Odd n := giuga_odd hn
  have hP_odd : ∀ p ∈ P, Odd p := fun p hp =>
    Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  have hprod : n = ∏ p ∈ P, p := giuga_prod_primeFactors hn
  have hres8 : (∑ p ∈ P, p) ≡ v + n [MOD 8] := giuga_residue_mod_8 hn hv
  have hresZ : (∑ p ∈ P, (p : ZMod 8)) = (v : ZMod 8) + (n : ZMod 8) := by
    have := (ZMod.natCast_eq_natCast_iff _ _ 8).mpr hres8
    simpa [Nat.cast_sum, Nat.cast_add] using this
  have hprodZ : (∏ p ∈ P, (p : ZMod 8)) = (n : ZMod 8) := by
    conv_rhs => rw [hprod]
    simp [Nat.cast_prod]
  have hid := sum_sub_prod_odd_zmod8 hP_odd
  rw [hresZ, hprodZ] at hid
  set k := (P.filter (fun p => p % 4 = 3)).card
  have hrec : k % 4 = 0 ∨ k % 4 = 1 := giuga_reciprocity_rule hn
  have hev : Even (k * (k - 1) / 2) := by
    rcases hrec with h0 | h1
    · have hk : k = 4 * (k / 4) := by omega
      rcases eq_or_ne (k / 4) 0 with hq0 | hqne
      · have hk0 : k = 0 := by omega
        simp [hk0]
      · set r := k / 4
        have hcalc : k * (k - 1) / 2 = (2 * r) * (4 * r - 1) := by
          rw [hk]
          have : (4 * r) * (4 * r - 1) = 2 * ((2 * r) * (4 * r - 1)) := by ring
          rw [this, Nat.mul_div_cancel_left _ (by omega)]
        rw [hcalc]
        exact ⟨r * (4 * r - 1), by ring⟩
    · have hk : k = 4 * (k / 4) + 1 := by omega
      set r := k / 4
      have hcalc : k * (k - 1) / 2 = (4 * r + 1) * (2 * r) := by
        rw [hk]
        have hsub : 4 * r + 1 - 1 = 4 * r := by omega
        rw [hsub]
        have : (4 * r + 1) * (4 * r) = 2 * ((4 * r + 1) * (2 * r)) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by omega)]
      rw [hcalc]
      exact ⟨(4 * r + 1) * r, by ring⟩
  have h4zero : (4 : ZMod 8) * (((k * (k - 1) / 2 : ℕ) : ZMod 8)) = 0 := by
    rcases hev with ⟨t, ht⟩
    rw [ht, Nat.cast_add]
    have : (4 : ZMod 8) * ((t : ZMod 8) + (t : ZMod 8)) = (8 : ZMod 8) * (t : ZMod 8) := by ring
    rw [this]
    change (0 : ZMod 8) * (t : ZMod 8) = 0
    simp
  rw [h4zero, sub_zero] at hid
  have hcardZ : (P.card : ZMod 8) = ((v + 1 : ℕ) : ZMod 8) := by
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination -hid
  exact (ZMod.natCast_eq_natCast_iff _ _ 8).mp hcardZ

/-! ### Part 2: General Bitmask Sets, Product Trees, and Prime-Exchange Bound -/

/-- Set of odd integers `2 * (lo + i) + 1` (`i < n`) selected by set bits of `mask`. -/
def maskOddSet (n lo mask : ℕ) : Finset ℕ :=
  ((Finset.range n).filter (fun i => mask.testBit i = true)).map
    ⟨fun i => 2 * (lo + i) + 1, fun a b h => by dsimp only at h; omega⟩

lemma testBit_one_shiftLeft_sub_one (B i : ℕ) :
    ((1 <<< B) - 1).testBit i = decide (i < B) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

lemma mem_maskOddSet_iff {n lo mask x : ℕ} :
    x ∈ maskOddSet n lo mask ↔
      ∃ i < n, mask.testBit i = true ∧ x = 2 * (lo + i) + 1 := by
  simp only [maskOddSet, Finset.mem_map, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, htb⟩, rfl⟩
    exact ⟨i, hi, htb, rfl⟩
  · rintro ⟨i, hi, htb, rfl⟩
    exact ⟨i, ⟨hi, htb⟩, rfl⟩

/-- Binary divide-and-conquer product over odd integers selected by `mask` on `[lo, lo + 2^d)`. -/
def prodMaskPow2 : ℕ → ℕ → ℕ → ℕ
  | 0, lo, mask => if (mask &&& 1) == 1 then 2 * lo + 1 else 1
  | d + 1, lo, mask =>
    if mask == 0 then 1
    else
      let half := 1 <<< d
      let lowM := mask &&& ((1 <<< half) - 1)
      let highM := mask >>> half
      prodMaskPow2 d lo lowM * prodMaskPow2 d (lo + half) highM

lemma maskOddSet_pow2_split (d lo mask : ℕ) :
    let half := 2 ^ d
    let lowM := mask &&& (2 ^ half - 1)
    let highM := mask >>> half
    Disjoint (maskOddSet half lo lowM) (maskOddSet half (lo + half) highM) ∧
      maskOddSet (2 ^ (d + 1)) lo mask =
        maskOddSet half lo lowM ∪ maskOddSet half (lo + half) highM := by
  dsimp only
  set half := 2 ^ d
  set lowM := mask &&& (2 ^ half - 1)
  set highM := mask >>> half
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxL hxR
    rcases mem_maskOddSet_iff.mp hxL with ⟨i, hi, _, rfl⟩
    rcases mem_maskOddSet_iff.mp hxR with ⟨j, _, _, heq⟩
    omega
  · ext x
    rw [Finset.mem_union, mem_maskOddSet_iff, mem_maskOddSet_iff, mem_maskOddSet_iff]
    constructor
    · rintro ⟨i, hi, htb, rfl⟩
      have h2d : 2 ^ (d + 1) = half + half := by rw [pow_succ, mul_two]
      rcases lt_or_ge i half with hlt | hge
      · left
        refine ⟨i, hlt, ?_, rfl⟩
        rw [Nat.testBit_and, htb, Nat.testBit_two_pow_sub_one, decide_eq_true_eq.mpr hlt,
          Bool.true_and]
      · right
        refine ⟨i - half, by omega, ?_, by omega⟩
        rw [Nat.testBit_shiftRight]
        have : half + (i - half) = i := by omega
        rwa [this]
    · rintro (⟨i, hi, htb, rfl⟩ | ⟨j, hj, htb, rfl⟩)
      · refine ⟨i, ?_, ?_, rfl⟩
        · have : 2 ^ (d + 1) = half + half := by rw [pow_succ, mul_two]
          omega
        · rw [Nat.testBit_and, Bool.and_eq_true] at htb
          exact htb.1
      · refine ⟨half + j, ?_, ?_, by omega⟩
        · have : 2 ^ (d + 1) = half + half := by rw [pow_succ, mul_two]
          omega
        · rwa [Nat.testBit_shiftRight] at htb

lemma testBit_zero_eq_and_one (mask : ℕ) :
    mask.testBit 0 = ((mask &&& 1) == 1) := by
  rw [testBit_eq_decide_div_mod, pow_zero, Nat.div_one, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one mask with h | h <;> simp [h]

lemma prod_maskOddSet_eq_prodMaskPow2 (d : ℕ) :
    ∀ lo mask : ℕ, (∏ p ∈ maskOddSet (2 ^ d) lo mask, p) = prodMaskPow2 d lo mask := by
  induction d with
  | zero =>
    intro lo mask
    unfold prodMaskPow2
    have h1 : 2 ^ 0 = 1 := rfl
    rw [h1]
    by_cases htb : mask.testBit 0 = true
    · have hand : ((mask &&& 1) == 1) = true := by rwa [← testBit_zero_eq_and_one]
      have hset : maskOddSet 1 lo mask = {2 * lo + 1} := by
        ext x
        rw [mem_maskOddSet_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨i, hi, _, rfl⟩; omega
        · rintro rfl; exact ⟨0, by omega, htb, by omega⟩
      rw [hset, Finset.prod_singleton, hand]; rfl
    · have htb_f : mask.testBit 0 = false := Bool.eq_false_iff.mpr htb
      have hand : ((mask &&& 1) == 1) = false := by rw [← testBit_zero_eq_and_one, htb_f]
      have hset : maskOddSet 1 lo mask = ∅ := by
        ext x
        rw [mem_maskOddSet_iff]
        simp only [Finset.notMem_empty, iff_false]
        rintro ⟨i, hi, ht, _⟩
        have hi0 : i = 0 := by omega
        rw [hi0, htb_f] at ht
        cases ht
      rw [hset, Finset.prod_empty, hand]; rfl
  | succ d ih =>
    intro lo mask
    unfold prodMaskPow2
    by_cases hm0 : mask = 0
    · subst hm0
      have hemp : maskOddSet (2 ^ (d + 1)) lo 0 = ∅ := by
        ext x
        rw [mem_maskOddSet_iff]
        simp
      simp [hemp]
    · have hm0b : (mask == 0) = false := beq_false_of_ne hm0
      rw [hm0b]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_shiftLeft]
      obtain ⟨hdisj, hunion⟩ := maskOddSet_pow2_split d lo mask
      rw [hunion, Finset.prod_union hdisj, ih, ih]

/-- **Division-free Prime-Product Exchange Lemma**:
If every element of `P` below `M` belongs to `Q`, every element of `Q` is `≤ M` (`1 ≤ M`),
`Q.card ≤ K`, and `K + r ≤ P.card`, then `(∏ q ∈ Q, q) * M ^ r ≤ ∏ p ∈ P, p`. -/
theorem prod_ge_of_low_subset_card {P Q : Finset ℕ} {M K r : ℕ}
    (hM : 1 ≤ M)
    (hsub : ∀ p ∈ P, p < M → p ∈ Q)
    (hQ_le : ∀ q ∈ Q, q ≤ M)
    (hQ_card : Q.card ≤ K)
    (hP_card : K + r ≤ P.card) :
    (∏ q ∈ Q, q) * M ^ r ≤ ∏ p ∈ P, p := by
  classical
  set P_low := P.filter (· < M)
  set P_high := P.filter (M ≤ ·)
  have hdisjP : Disjoint P_low P_high := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    omega
  have hunionP : P_low ∪ P_high = P := by
    ext x
    simp only [P_low, P_high, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      rcases lt_or_ge x M with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hP_card_eq : P.card = P_low.card + P_high.card := by
    rw [← hunionP, Finset.card_union_of_disjoint hdisjP]
  have hP_prod_eq : (∏ p ∈ P, p) = (∏ p ∈ P_low, p) * ∏ p ∈ P_high, p := by
    rw [← hunionP, Finset.prod_union hdisjP]
  have hPlow_sub : P_low ⊆ Q := by
    intro x hx
    exact hsub x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hdisjQ : Disjoint P_low (Q \ P_low) := Finset.disjoint_sdiff
  have hunionQ : P_low ∪ (Q \ P_low) = Q := Finset.union_sdiff_of_subset hPlow_sub
  have hQ_card_eq : Q.card = P_low.card + (Q \ P_low).card := by
    conv_lhs => rw [← hunionQ]
    exact Finset.card_union_of_disjoint hdisjQ
  have hQ_prod_eq : (∏ q ∈ Q, q) = (∏ p ∈ P_low, p) * ∏ q ∈ Q \ P_low, q := by
    conv_lhs => rw [← hunionQ]
    exact Finset.prod_union hdisjQ
  set d := (Q \ P_low).card
  have hdr : d + r ≤ P_high.card := by omega
  have hsdiff_le : (∏ q ∈ Q \ P_low, q) ≤ M ^ d := by
    calc
      (∏ q ∈ Q \ P_low, q) ≤ ∏ _q ∈ Q \ P_low, M :=
        Finset.prod_le_prod fun q hq => hQ_le q (Finset.mem_sdiff.mp hq).1
      _ = M ^ d := Finset.prod_const M
  have hhigh_ge : M ^ (d + r) ≤ ∏ p ∈ P_high, p := by
    calc
      M ^ (d + r) ≤ M ^ P_high.card := Nat.pow_le_pow_right hM hdr
      _ = ∏ _p ∈ P_high, M := (Finset.prod_const M).symm
      _ ≤ ∏ p ∈ P_high, p :=
        Finset.prod_le_prod fun p hp => (Finset.mem_filter.mp hp).2
  calc
    (∏ q ∈ Q, q) * M ^ r
        = (∏ p ∈ P_low, p) * ((∏ q ∈ Q \ P_low, q) * M ^ r) := by
          rw [hQ_prod_eq, mul_assoc]
    _ ≤ (∏ p ∈ P_low, p) * (M ^ d * M ^ r) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsdiff_le)
    _ = (∏ p ∈ P_low, p) * M ^ (d + r) := by rw [← pow_add]
    _ ≤ (∏ p ∈ P_low, p) * (∏ p ∈ P_high, p) := Nat.mul_le_mul_left _ hhigh_ge
    _ = ∏ p ∈ P, p := hP_prod_eq.symm

/-! ### Part 3: Unconditional 2-Leaf (`d = 2`, `Λ = 3000`) Pure-Kernel Certificate (`≥ 578` Primes) -/

/-- Binary radix trie mapping `d`-bit indices to accumulated nonnegative integer edge weights. -/
inductive Trie : Type
  | zero : Trie
  | leaf : ℕ → Trie
  | node : Trie → Trie → Trie

/-- Well-formedness of a `Trie` at depth `d`. -/
def Trie.WF : ℕ → Trie → Prop
  | _, .zero => True
  | 0, .leaf _ => True
  | 0, .node _ _ => False
  | _ + 1, .leaf _ => False
  | d + 1, .node l r => Trie.WF d l ∧ Trie.WF d r

/-- Lookup index `idx` in a depth-`d` `Trie`. -/
def Trie.get : ℕ → Trie → ℕ → ℕ
  | _, .zero, _ => 0
  | 0, .leaf v, _ => v
  | 0, .node _ _, _ => 0
  | _ + 1, .leaf _, _ => 0
  | d + 1, .node l r, idx =>
    if idx % 2 == 0 then Trie.get d l (idx / 2) else Trie.get d r (idx / 2)

/-- Singleton depth-`d` `Trie` having `val` at `idx` and `0` elsewhere. -/
def Trie.singleton : ℕ → ℕ → ℕ → Trie
  | 0, _, val => .leaf val
  | d + 1, idx, val =>
    if idx % 2 == 0 then .node (Trie.singleton d (idx / 2) val) .zero
    else .node .zero (Trie.singleton d (idx / 2) val)

/-- Pointwise merge (sum) of two `Trie`s. -/
def Trie.merge : Trie → Trie → Trie
  | .zero, b => b
  | a, .zero => a
  | .leaf u, .leaf v => .leaf (u + v)
  | .node l₁ r₁, .node l₂ r₂ => .node (Trie.merge l₁ l₂) (Trie.merge r₁ r₂)
  | _, _ => .zero

lemma Trie.wf_zero (d : ℕ) : Trie.WF d .zero := by
  cases d <;> trivial

lemma Trie.get_zero (d j : ℕ) : Trie.get d .zero j = 0 := by
  cases d <;> rfl

lemma Trie.wf_singleton (d idx val : ℕ) : Trie.WF d (Trie.singleton d idx val) := by
  induction d generalizing idx with
  | zero => trivial
  | succ d ih =>
    unfold Trie.singleton
    split_ifs
    · exact ⟨ih (idx / 2), Trie.wf_zero d⟩
    · exact ⟨Trie.wf_zero d, ih (idx / 2)⟩

lemma Trie.wf_merge {d : ℕ} {a b : Trie} (ha : Trie.WF d a) (hb : Trie.WF d b) :
    Trie.WF d (Trie.merge a b) := by
  induction d generalizing a b with
  | zero =>
    match a, b with
    | .zero, b => exact hb
    | .leaf _, .zero => exact ha
    | .leaf _, .leaf _ => trivial
    | .node _ _, _ => cases ha
    | _, .node _ _ => cases hb
  | succ d ih =>
    match a, b with
    | .zero, b => exact hb
    | .node _ _, .zero => exact ha
    | .node l₁ r₁, .node l₂ r₂ => exact ⟨ih ha.1 hb.1, ih ha.2 hb.2⟩
    | .leaf _, _ => cases ha
    | _, .leaf _ => cases hb

lemma Trie.get_singleton (d : ℕ) :
    ∀ {idx j : ℕ} (val : ℕ), idx < 2 ^ d → j < 2 ^ d →
      Trie.get d (Trie.singleton d idx val) j = if j = idx then val else 0 := by
  induction d with
  | zero =>
    intro idx j val hi hj
    have hi0 : idx = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    rfl
  | succ d ih =>
    intro idx j val hi hj
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
    have hi2 : idx / 2 < 2 ^ d := by omega
    have hj2 : j / 2 < 2 ^ d := by omega
    unfold Trie.singleton Trie.get
    rcases Nat.mod_two_eq_zero_or_one idx with hmi | hmi <;>
      rcases Nat.mod_two_eq_zero_or_one j with hmj | hmj <;>
      simp [hmi, hmj]
    · rw [ih val hi2 hj2]
      have heq : (j = idx) ↔ (j / 2 = idx / 2) := by omega
      simp [heq]
    · have hne : j ≠ idx := by omega
      simp [hne, Trie.get]
    · have hne : j ≠ idx := by omega
      simp [hne, Trie.get]
    · rw [ih val hi2 hj2]
      have heq : (j = idx) ↔ (j / 2 = idx / 2) := by omega
      simp [heq]

lemma Trie.get_merge {d : ℕ} {a b : Trie} (ha : Trie.WF d a) (hb : Trie.WF d b) (j : ℕ) :
    Trie.get d (Trie.merge a b) j = Trie.get d a j + Trie.get d b j := by
  induction d generalizing a b j with
  | zero =>
    match a, b with
    | .zero, b => change Trie.get 0 b j = 0 + Trie.get 0 b j; omega
    | .leaf u, .zero => change u = u + 0; omega
    | .leaf u, .leaf v => rfl
    | .node _ _, _ => cases ha
    | _, .node _ _ => cases hb
  | succ d ih =>
    match a, b with
    | .zero, b =>
      change Trie.get (d + 1) b j = 0 + Trie.get (d + 1) b j
      omega
    | .node l₁ r₁, .zero =>
      change Trie.get (d + 1) (.node l₁ r₁) j = Trie.get (d + 1) (.node l₁ r₁) j + 0
      omega
    | .node l₁ r₁, .node l₂ r₂ =>
      change (if j % 2 == 0 then Trie.get d (Trie.merge l₁ l₂) (j / 2)
          else Trie.get d (Trie.merge r₁ r₂) (j / 2)) =
        (if j % 2 == 0 then Trie.get d l₁ (j / 2) else Trie.get d r₁ (j / 2)) +
          (if j % 2 == 0 then Trie.get d l₂ (j / 2) else Trie.get d r₂ (j / 2))
      split_ifs
      · exact ih ha.1 hb.1 (j / 2)
      · exact ih ha.2 hb.2 (j / 2)
    | .leaf _, _ => cases ha
    | _, .leaf _ => cases hb

/-- Parallel unpacking of `cnt` 64-bit conflict edges `(q | r<<12 | η<<24)` into a depth-11 `Trie`
and total `η` sum, checking `3 ≤ q < r < 3000`, `Odd q`, `Odd r`, and `q ∣ r - 1`. -/
def evalEdgesPow2 : ℕ → ℕ → ℕ → Trie × ℕ × Bool
  | 0, cnt, words =>
    if cnt == 0 then (.zero, 0, true)
    else
      let w := words &&& 0xFFFFFFFFFFFFFFFF
      let q := w &&& 0xFFF
      let r := (w >>> 12) &&& 0xFFF
      let eta := w >>> 24
      let ok := decide (3 ≤ q ∧ q < r ∧ r < 3000 ∧ q % 2 = 1 ∧ r % 2 = 1 ∧ (r - 1) % q = 0)
      let tq := Trie.singleton 11 ((q - 1) / 2) eta
      let tr := Trie.singleton 11 ((r - 1) / 2) eta
      (Trie.merge tq tr, eta, ok)
  | d + 1, cnt, words =>
    if cnt == 0 then (.zero, 0, true)
    else
      let half := 1 <<< d
      if cnt ≤ half then evalEdgesPow2 d cnt words
      else
        let shift := 64 * half
        let lowW := words &&& ((1 <<< shift) - 1)
        let highW := words >>> shift
        let (tL, sumL, okL) := evalEdgesPow2 d half lowW
        let (tR, sumR, okR) := evalEdgesPow2 d (cnt - half) highW
        (Trie.merge tL tR, sumL + sumR, okL && okR)

lemma evalEdgesPow2_sound (d : ℕ) {A : Finset ℕ} (hA : IsNormalOddPrimeSet A)
    (hA_lt : ∀ x ∈ A, x < 3000) :
    ∀ cnt words : ℕ,
      let res := evalEdgesPow2 d cnt words
      Trie.WF 11 res.1 ∧
        (res.2.2 = true → (∑ x ∈ A, Trie.get 11 res.1 ((x - 1) / 2)) ≤ res.2.1) := by
  induction d with
  | zero =>
    intro cnt words
    unfold evalEdgesPow2
    by_cases hc : cnt = 0
    · simp [hc, Trie.WF, Trie.get]
    · have hcb : (cnt == 0) = false := beq_false_of_ne hc
      simp only [hcb, Bool.false_eq_true, ↓reduceIte]
      set w := words &&& 0xFFFFFFFFFFFFFFFF
      set q := w &&& 0xFFF
      set r := (w >>> 12) &&& 0xFFF
      set eta := w >>> 24
      have hwf : Trie.WF 11 (Trie.merge (Trie.singleton 11 ((q - 1) / 2) eta)
          (Trie.singleton 11 ((r - 1) / 2) eta)) :=
        Trie.wf_merge (Trie.wf_singleton ..) (Trie.wf_singleton ..)
      refine ⟨hwf, fun hok => ?_⟩
      simp only [decide_eq_true_eq] at hok
      rcases hok with ⟨hq3, hlt, hr3000, hqodd, hrodd, hdvd_mod⟩
      have hq_idx : (q - 1) / 2 < 2 ^ 11 := by norm_num; omega
      have hr_idx : (r - 1) / 2 < 2 ^ 11 := by norm_num; omega
      have hterm : ∀ x ∈ A,
          Trie.get 11 (Trie.merge (Trie.singleton 11 ((q - 1) / 2) eta)
            (Trie.singleton 11 ((r - 1) / 2) eta)) ((x - 1) / 2) =
            (if x = q then eta else 0) + (if x = r then eta else 0) := by
        intro x hx
        have hx_odd : Odd x := (hA.1 x hx).2
        have hx_lt : x < 3000 := hA_lt x hx
        have hx_idx : (x - 1) / 2 < 2 ^ 11 := by norm_num; omega
        rw [Trie.get_merge (Trie.wf_singleton ..) (Trie.wf_singleton ..),
          Trie.get_singleton 11 eta hq_idx hx_idx,
          Trie.get_singleton 11 eta hr_idx hx_idx]
        have h2x : 2 * ((x - 1) / 2) + 1 = x := by rcases hx_odd with ⟨t, rfl⟩; omega
        have h2q : 2 * ((q - 1) / 2) + 1 = q := by omega
        have h2r : 2 * ((r - 1) / 2) + 1 = r := by omega
        have heq_q : ((x - 1) / 2 = (q - 1) / 2) ↔ (x = q) := by omega
        have heq_r : ((x - 1) / 2 = (r - 1) / 2) ↔ (x = r) := by omega
        simp [heq_q, heq_r]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hsum_q : (∑ x ∈ A, if x = q then eta else 0) = if q ∈ A then eta else 0 := by
        simp [Finset.sum_ite_eq']
      have hsum_r : (∑ x ∈ A, if x = r then eta else 0) = if r ∈ A then eta else 0 := by
        simp [Finset.sum_ite_eq']
      rw [hsum_q, hsum_r]
      have hnotboth : ¬ (q ∈ A ∧ r ∈ A) := by
        rintro ⟨hqA, hrA⟩
        exact hA.2 q hqA r hrA hlt (Nat.dvd_of_mod_eq_zero hdvd_mod)
      by_cases hqA : q ∈ A <;> by_cases hrA : r ∈ A
      · exfalso; exact hnotboth ⟨hqA, hrA⟩
      · simp [hqA, hrA]
      · simp [hqA, hrA]
      · simp [hqA, hrA]
  | succ d ih =>
    intro cnt words
    unfold evalEdgesPow2
    by_cases hc : cnt = 0
    · simp [hc, Trie.WF, Trie.get]
    · have hcb : (cnt == 0) = false := beq_false_of_ne hc
      simp only [hcb, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : cnt ≤ 1 <<< d
      · simp only [hle, ↓reduceIte]
        exact ih cnt words
      · simp only [hle, ↓reduceIte]
        set resL := evalEdgesPow2 d (1 <<< d) (words &&& ((1 <<< (64 * (1 <<< d))) - 1))
        set resR := evalEdgesPow2 d (cnt - (1 <<< d)) (words >>> (64 * (1 <<< d)))
        have ihL := ih (1 <<< d) (words &&& ((1 <<< (64 * (1 <<< d))) - 1))
        have ihR := ih (cnt - (1 <<< d)) (words >>> (64 * (1 <<< d)))
        refine ⟨Trie.wf_merge ihL.1 ihR.1, fun hok => ?_⟩
        rw [Bool.and_eq_true] at hok
        have hterm : ∀ x ∈ A,
            Trie.get 11 (Trie.merge resL.1 resR.1) ((x - 1) / 2) =
              Trie.get 11 resL.1 ((x - 1) / 2) + Trie.get 11 resR.1 ((x - 1) / 2) :=
          fun x _ => Trie.get_merge ihL.1 ihR.1 _
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
        exact Nat.add_le_add (ihL.2 hok.1) (ihR.2 hok.2)

/-- Vertex slack term at bit index `k` (`p = 2 * k + 1`) for `Λ = 3000`, `SCALE = 10^6`. -/
def slackTerm3000 (skipThree : Bool) (incTrie : Trie) (k : ℕ) : ℕ :=
  let p := 2 * k + 1
  if k < 2 || 3000 ≤ p || (skipThree && decide ((2 * k) % 3 = 0)) then 0
  else
    let wUp := (3000000000 + p - 1) / p - 1000000
    wUp - Trie.get 11 incTrie k

/-- Binary divide-and-conquer sum of `slackTerm3000` over set bits of `mask` in `[lo, lo + 2^d)`. -/
def sumSlack3000Pow2 (skipThree : Bool) (incTrie : Trie) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, mask =>
    if (mask &&& 1) == 1 then slackTerm3000 skipThree incTrie lo else 0
  | d + 1, lo, mask =>
    if mask == 0 then 0
    else
      let half := 1 <<< d
      let lowM := mask &&& ((1 <<< half) - 1)
      let highM := mask >>> half
      sumSlack3000Pow2 skipThree incTrie d lo lowM +
        sumSlack3000Pow2 skipThree incTrie d (lo + half) highM

lemma sum_maskOddSet_slack_eq (skipThree : Bool) (incTrie : Trie) (d : ℕ) :
    ∀ lo mask : ℕ,
      (∑ p ∈ maskOddSet (2 ^ d) lo mask, slackTerm3000 skipThree incTrie ((p - 1) / 2)) =
        sumSlack3000Pow2 skipThree incTrie d lo mask := by
  induction d with
  | zero =>
    intro lo mask
    unfold sumSlack3000Pow2
    have h1 : 2 ^ 0 = 1 := rfl
    rw [h1]
    by_cases htb : mask.testBit 0 = true
    · have hand : ((mask &&& 1) == 1) = true := by rwa [← testBit_zero_eq_and_one]
      have hset : maskOddSet 1 lo mask = {2 * lo + 1} := by
        ext x
        rw [mem_maskOddSet_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨i, hi, _, rfl⟩; omega
        · rintro rfl; exact ⟨0, by omega, htb, by omega⟩
      have hidx : (2 * lo + 1 - 1) / 2 = lo := by omega
      rw [hset, Finset.sum_singleton, hidx, hand]; rfl
    · have htb_f : mask.testBit 0 = false := Bool.eq_false_iff.mpr htb
      have hand : ((mask &&& 1) == 1) = false := by rw [← testBit_zero_eq_and_one, htb_f]
      have hset : maskOddSet 1 lo mask = ∅ := by
        ext x
        rw [mem_maskOddSet_iff]
        simp only [Finset.notMem_empty, iff_false]
        rintro ⟨i, hi, ht, _⟩
        have hi0 : i = 0 := by omega
        rw [hi0, htb_f] at ht
        cases ht
      rw [hset, Finset.sum_empty, hand]; rfl
  | succ d ih =>
    intro lo mask
    unfold sumSlack3000Pow2
    by_cases hm0 : mask = 0
    · subst hm0
      have hemp : maskOddSet (2 ^ (d + 1)) lo 0 = ∅ := by
        ext x; rw [mem_maskOddSet_iff]; simp
      simp [hemp]
    · have hm0b : (mask == 0) = false := beq_false_of_ne hm0
      rw [hm0b]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_shiftLeft]
      obtain ⟨hdisj, hunion⟩ := maskOddSet_pow2_split d lo mask
      rw [hunion, Finset.sum_union hdisj, ih, ih]

/-- Packed 312 active conflict edges for depth-2 leaf `S = ∅` (`Λ = 3000`, `SCALE = 10^6`). -/
def packedEdges3000Empty : ℕ :=
  0x8286b575ab000000a42db3f59f000000fad0b035810000035b6999b4cd0000068cc5833419000006ee3180f40700000d040465332900000038ceb8d2e30000007a33b5d2d70000123a5b5572ab0000146b9e50328100000338c79ad26b000004910090524100001da9ff3fb1fd0000083a7379d1e700000b27df6c51b1000025c8d635f1af000003f36694f18d0000052fac8bf17500000f66e25d5175000005853489b16f000030686e2cf167000007c7767c314b000009428874b13700000baf316a311b00000ce06d65b10f00000dbb6162b10700000e688960710100004bbf771f70fb00001060685a70f10000011b82aed0e900001176455770e9000052c36f1d30e9000003e70c9550c700002a2d5431d0c7000008728078b0c100002bf5d83050c10000008ae3b510b500001ada9243f0b500001ccca040f0ad000074a95e15b0ad000002496aa310a3000036d7c528d0a30000023bafa3906d000003d29a95f06d00001ab30b44306d0000061f3f85d06b00002627e835906b000037eede28306b00000af1ae6d306100000e37a261106100001fe27f3cb0610000666b13185061000001e127a6f059000006297e85905900001b901a42d0590000f079a10b3059000001f845a61053000007b5b57c905300001ea7c43e505300004c7a391f3053000102d9e80a705300000adab86d904900000d3a11647049000024f01136d04900005903f11b704900008cf97c12504900000781147db04300000d310164904300009ae9e110d043000000e645b1103b000008f96e76103b000017807d49d03b00001bcdfa42703b0000314e502c503b00002055be0530290000055a178ad025000007a40f7cf02500000a806f6f102500000fa67b5c902500003def8e2510250000be04330df025000123f7150950250000015eff9ef01f000007bdfc5d101f00000cdc8345d01f00002b706117501f000002d3d79e3017000007df4e7bb01700000c5e05679017000010d1e9593017000011e373565017000018831e47f01700001dee1d3f5017000027f5c233d017000032fcdf2b30170000540a091cd017000095ffb511501700013a114e08b0170003beb4dc02f017000000cc27b23013000001b3a3a8b01300000429a5935013000004cf4d8e901300000526578c301300000709dd805013000008d24576d01300000a5b886fb01300000e1a976170130000165af74c101300001a3e2f44f01300002ce4e62f9013000040e8f523b013000054e8881c901300005dfe211a30130000b8a3550e50130000e068770bf0130000012787ae5011000001c707a7f011000002af8a9f70110000043ed492b011000007f1507b5011000009351d74f01100000ea4105fb011000012602655101100001519bc4eb01100001980f846301100001d93783fd0110000228d623970110000377e3228701100003b6acd265011000060a9f4199011000085d99313301100013ee0130890110001ad2c060670110000005114b7b00d00000098e5b4700d000000bdc9b2d00d000003ded995900d0000044ba092500d000005345a8bd00d000006bd0f82100d0000074d617ed00d000008344979f00d0000092e6d75100d000009868073700d00000d1ef164d00d00000f9bcf5cb00d0000133cc352f00d000013ed3f51500d00001564424e100d0000162bb94c700d000017d53949300d000021986c3a900d000026081235b00d0000345b932a500d00003d299c25700d0000489a8e20900d00005812ea1bb00d000082fdd913900d0001144f7909d00d0000a716ee08300d000234305c04f00d000350723e03500d000000c1f4aa900b000000d367a9300b000000f72ba6700b000001ffe894900b0000022e6591d00b00000277838db00b000002dfe588300b00000333e384100b0000036edc81500b000005351f6f700b0000081f7b5ad00b000008200158100b00000a4b444fd00b0000108a2d3b300b0000179d702d700b000010c4942ab00b0000300c4f18d00b00003935ac16100b00005458c80c700b00006f805d05900b0001ec5c8204300b0001090a5501700b00000028cab99007000000616db6f007000000c385b29007000000d7b8b1b0070000011587af100700000180c3aab007000001c3c9a8100700000208efa570070000022079a49007000002689fa1f007000002b3259f5007000002e6349d9007000003866e985007000003a237977007000003f78794d0070000044fe89230070000048c9c907007000004ab848f9007000004ea798dd0070000056d2a8a50070000061a2385f0070000063e19851007000006acdf8270070000076fbe7e1007000007985a7d30070000086c3878d007000009211875500700000b4f1e6bb00700000b86d56ad00700000c339968300700000d67bb63d00700000da8a062f00700000f47775db00700000fdc455bf007000010c66b59500700001214e555d007000013df6c517007000014411a5090070000181a1048b00700001a9f6444500700001c4bd941b00700001e1bf93f1007000020146b3c7007000020c6723b9007000022fd5d38f007000024954537300700002817f233b00700002d36442f500700002e59f62e70070000320af12bd007000034c2752a10070000363461293007000039497727700700003aeedd2690070000446d6d22300700004df8dc1eb0070000539c3a1cf007000056b16b1c100700005d79431a500700006985f017b007000078937e151007000093a57d1190070000b0462e0ef0070000c9b0da0d30070000d91bcb0c50070001592f6007f007000185d78107100700013abd490470070004194ed202b00700061b3c9401d0070000002622b9b0050000012484ae7005000001711cab5005000001a06ba9700500000234daa3d0050000037e8d989005000003ba4996b0050000040c49943005000004365592f00500000513c68cb005000005ec9787100500000638ee8530050000066d0883f00500000956c5745005000009bdf172700500000a04a071300500000a288e70900500000b08cc6cd00500000b57056b900500000cfb1665500500000d556564100500000de12c62300500000f09615e700500000fc78e5ab00500001364df529005000014330550b005000015ed744cf005000016db3f4b100500001be2c242500500001635f440700500001eeeee3df00500002163423ad005000024b3663710050000287f813350050000292f8132b00500002db1f22ef005000035fe92295005000023bc1e28100500003ce8812590050000455b0721d0050000352a971af005000062e591191005000073425f14b00500007aac1713700500008cc7f210f00500005b5e890fb00500009e4edd0f10050000d240c50b500500011fe55e0970050000a716ee0830050001b5f8fb06500500013abd490470050002df2c6803d00500042ce72d029005000573fc1301f005000ba457a400b005

/-- Packed 108 active conflict edges for depth-2 leaf `S = {3}` (`Λ = 3000`, `SCALE = 10^6`). -/
def packedEdges3000Three : ℕ :=
  0x14ebb75db000000a42db3f59f000000fad0b035810000035b6999b4cd00000372c898f4c70000068cc583341900000d04046533290000123a5b5572ab0000137253527293000013c3e551b28d0000174e544a325100001da9ff3fb1fd0000274d463471a3000030686e2cf16700003eb98d24b12500000600bd86910d000003a2379770ad000074a95e15b0ad000006acdf8270950000171cad4a90950000005114b7b07100000da8a062f0710000ba66340e30710000f079a10b3059000001f845a610530000181a1048b053000102d9e80a705300000028cab990350000045cca91d03500000bb7526a103500002e59f62e703500019c8ec806b035000000d7b8b1b01d00001496894fd01d00001a3e2f44f01d000022041f3a101d0000b534d10e901d0002f89ca203b01d000003ded9959017000007df4e7bb017000010d1e9593017000014411a50901700001dee1d3f501700003d299c2570170003beb4dc02f0170000012787ae5011000001c707a7f011000007f1507b501100000c339968301100001519bc4eb011000020c6723b90110000377e3228701100005812ea1bb0110000b0462e0ef01100013ee013089011000000bdc9b2d0050000011587af1005000001711cab5005000001a06ba9700500000234daa3d005000002689fa1f005000002d3d79e30050000037e8d989005000003ba4996b005000003f78794d005000004365592f0050000061f3f85d0050000066d0883f005000006bd0f821005000008728078b005000008d24576d005000009351d74f00500000a04a071300500000b57056b900500000d556564100500000de12c62300500000f09615e700500000fa67b5c90050000104a145ab0050000126026551005000013ed3f515005000017807d49d005000018831e47f00500001ab30b44300500001be2c242500500001d242540700500001fe27f3cb00500002163423ad005000022fd5d38f005000024b3663710050000287f8133500500002ce4e62f90050000320af12bd00500003827bc2810050000489a8e20900500004df8dc1eb0050000540a091cd00500005af36d1af005000062e591191005000083ee9f137005000093a57d1190050000a71e000fb0050000e068770bf00500014e2ddc0830050001b5f8fb0650050002757a9204700500044d3cec0290050010323aa900b005

/-- Computable verifier for a single leaf `(skipThree, d, cnt, packed, needLo, targetK)` at `Λ = 3000`. -/
def checkLeaf3000 (skipThree : Bool) (d cnt packed needLo targetK : ℕ) : Bool :=
  let mask1500 := survivorMask &&& ((1 <<< 1500) - 1)
  let (t, eta, ok) := evalEdgesPow2 d cnt packed
  let slack := sumSlack3000Pow2 skipThree t 11 0 mask1500
  ok && decide (targetK * 1000000 + (eta + slack) ≤ 3000 * needLo)

/-- Pure-kernel GMP/WHNF verification of the `S = ∅` leaf at `Λ = 3000` (zero `native_decide`). -/
lemma checkLeaf3000_empty :
    checkLeaf3000 false 9 312 packedEdges3000Empty 1000000 574 = true := rfl

/-- Pure-kernel GMP/WHNF verification of the `S = {3}` leaf at `Λ = 3000` (zero `native_decide`). -/
lemma checkLeaf3000_three :
    checkLeaf3000 true 7 108 packedEdges3000Three 666666 586 = true := rfl

lemma leaf3000_tail_bound {S T : Finset ℕ} {skipThree : Bool}
    {d cnt packed needLo targetK : ℕ}
    (hT : IsNormalOddPrimeSet T)
    (hTail : ∀ x ∈ T, IsTailPrime S 5 x)
    (hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ))
    (hneed_lo : (needLo : ℝ) / 1000000 ≤ need S)
    (hskip : skipThree = true → 3 ∈ S)
    (hcheck_b : checkLeaf3000 skipThree d cnt packed needLo targetK = true) :
    targetK + 1 ≤ T.card := by
  unfold checkLeaf3000 at hcheck_b
  set mask1500 := survivorMask &&& ((1 <<< 1500) - 1)
  set res := evalEdgesPow2 d cnt packed
  set slack := sumSlack3000Pow2 skipThree res.1 11 0 mask1500
  have hcheck : res.2.2 = true ∧ targetK * 1000000 + (res.2.1 + slack) ≤ 3000 * needLo := by
    change (res.2.2 && decide (targetK * 1000000 + (res.2.1 + slack) ≤ 3000 * needLo)) = true at hcheck_b
    rw [Bool.and_eq_true, decide_eq_true_eq] at hcheck_b
    exact hcheck_b
  set A := T.filter (· < 3000)
  have hA_norm : IsNormalOddPrimeSet A := hT.subset (Finset.filter_subset _ _)
  have hA_lt : ∀ x ∈ A, x < 3000 := fun _ hx => (Finset.mem_filter.mp hx).2
  have hsound := (evalEdgesPow2_sound d hA_norm hA_lt cnt packed).2 hcheck.1
  have hA_sub_mask : A ⊆ maskOddSet (2 ^ 11) 0 mask1500 := by
    intro x hx
    have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
    have hxlt : x < 3000 := (Finset.mem_filter.mp hx).2
    obtain ⟨hpr, hodd, _, _⟩ := hTail x hxT
    rw [mem_maskOddSet_iff]
    refine ⟨(x - 1) / 2, by norm_num; omega, ?_, by rcases hodd with ⟨t, rfl⟩; omega⟩
    have hsurv := survivorMask_testBit_of_odd_prime hpr hodd (by omega)
    rw [Nat.testBit_and, hsurv, testBit_one_shiftLeft_sub_one]
    simp only [Bool.true_and, decide_eq_true_eq]
    omega
  have hslack_le :
      (∑ x ∈ A, slackTerm3000 skipThree res.1 ((x - 1) / 2)) ≤ slack := by
    dsimp only [slack]
    rw [← sum_maskOddSet_slack_eq skipThree res.1 11 0 mask1500]
    exact Finset.sum_le_sum_of_subset hA_sub_mask
  have hwUp_sum :
      (∑ x ∈ A, ((3000000000 + x - 1) / x - 1000000)) ≤ res.2.1 + slack := by
    have hpoint : ∀ x ∈ A,
        (3000000000 + x - 1) / x - 1000000 ≤
          Trie.get 11 res.1 ((x - 1) / 2) + slackTerm3000 skipThree res.1 ((x - 1) / 2) := by
      intro x hx
      have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
      have hxlt : x < 3000 := (Finset.mem_filter.mp hx).2
      obtain ⟨_, hodd, hge5, hnotdvd⟩ := hTail x hxT
      set k := (x - 1) / 2
      have hk_eq : 2 * k + 1 = x := by rcases hodd with ⟨t, rfl⟩; omega
      have hb1 : decide (k < 2) = false := decide_eq_false (by omega)
      have hb2 : decide (3000 ≤ 2 * k + 1) = false := decide_eq_false (by omega)
      have hnot3 : (skipThree && decide ((2 * k) % 3 = 0)) = false := by
        cases hst : skipThree
        · rfl
        · have h3S : 3 ∈ S := hskip hst
          have hnd : ¬ (3 ∣ x - 1) := hnotdvd 3 h3S
          have h2k : x - 1 = 2 * k := by omega
          rw [h2k] at hnd
          have hmod : ¬ ((2 * k) % 3 = 0) := fun hm => hnd (Nat.dvd_of_mod_eq_zero hm)
          simp [hmod]
      have hslack_eq : slackTerm3000 skipThree res.1 k =
          ((3000000000 + x - 1) / x - 1000000) - Trie.get 11 res.1 k := by
        unfold slackTerm3000
        dsimp only
        rw [hb1, hb2, hnot3]
        simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk_eq]
      rw [hslack_eq]
      omega
    calc
      (∑ x ∈ A, ((3000000000 + x - 1) / x - 1000000))
          ≤ ∑ x ∈ A, (Trie.get 11 res.1 ((x - 1) / 2) +
              slackTerm3000 skipThree res.1 ((x - 1) / 2)) := Finset.sum_le_sum hpoint
      _ = (∑ x ∈ A, Trie.get 11 res.1 ((x - 1) / 2)) +
            ∑ x ∈ A, slackTerm3000 skipThree res.1 ((x - 1) / 2) := Finset.sum_add_distrib
      _ ≤ res.2.1 + slack := Nat.add_le_add hsound hslack_le
  let w : ℕ → ℝ := fun x => (1000000 : ℝ) * ((3000 : ℝ) / (x : ℝ) - 1)
  have hnonpos : ∀ x ∈ T, x ∉ A → w x ≤ 0 := by
    intro x hx hxA
    have hge : 3000 ≤ x := by
      by_contra hlt
      exact hxA (Finset.mem_filter.mpr ⟨hx, Nat.lt_of_not_ge hlt⟩)
    have hgeR : (3000 : ℝ) ≤ (x : ℝ) := Nat.cast_le.mpr hge
    have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
    have hdiv : (3000 : ℝ) / (x : ℝ) ≤ 1 := (div_le_one hxpos).mpr hgeR
    dsimp only [w]
    nlinarith
  have hT_le_A : (∑ x ∈ T, w x) ≤ ∑ x ∈ T ∩ A, w x := sum_le_sum_inter_of_nonpos hnonpos
  have hinter : T ∩ A = A := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  rw [hinter] at hT_le_A
  have hw_le_nat : ∀ x ∈ A, w x ≤ (((3000000000 + x - 1) / x - 1000000 : ℕ) : ℝ) := by
    intro x hx
    have hxT : x ∈ T := (Finset.mem_filter.mp hx).1
    have hxlt : x < 3000 := (Finset.mem_filter.mp hx).2
    have hge5 : 5 ≤ x := (hTail x hxT).2.2.1
    have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    set q := (3000000000 + x - 1) / x
    have hq_ge : 1000000 ≤ q := by
      have : 1000000 * x ≤ 3000000000 + x - 1 := by omega
      exact (Nat.le_div_iff_mul_le (by omega : 0 < x)).mpr this
    have hmul_ge : 3000000000 ≤ x * q := by
      have h1 : x * q + (3000000000 + x - 1) % x = 3000000000 + x - 1 :=
        Nat.div_add_mod (3000000000 + x - 1) x
      have h2 := Nat.mod_lt (3000000000 + x - 1) (by omega : 0 < x)
      generalize x * q = m at h1 ⊢
      omega
    have hmulR : (3000000000 : ℝ) ≤ (x : ℝ) * (q : ℝ) := by exact_mod_cast hmul_ge
    have hdivR : (3000000000 : ℝ) / (x : ℝ) ≤ (q : ℝ) :=
      (div_le_iff₀ hxpos).mpr (by linarith)
    rw [Nat.cast_sub hq_ge]
    dsimp only [w]
    have hrew : (1000000 : ℝ) * ((3000 : ℝ) / (x : ℝ) - 1) =
        (3000000000 : ℝ) / (x : ℝ) - (1000000 : ℝ) := by ring
    linarith
  have hA_le_ub : (∑ x ∈ A, w x) ≤ (res.2.1 : ℝ) + (slack : ℝ) := by
    calc
      (∑ x ∈ A, w x) ≤ ∑ x ∈ A, (((3000000000 + x - 1) / x - 1000000 : ℕ) : ℝ) :=
        Finset.sum_le_sum hw_le_nat
      _ = ((∑ x ∈ A, ((3000000000 + x - 1) / x - 1000000) : ℕ) : ℝ) := (Nat.cast_sum _ _).symm
      _ ≤ ((res.2.1 + slack : ℕ) : ℝ) := Nat.cast_le.mpr hwUp_sum
      _ = (res.2.1 : ℝ) + (slack : ℝ) := Nat.cast_add _ _
  have hsum_w : (∑ x ∈ T, w x) =
      (1000000 : ℝ) * ((3000 : ℝ) * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - (T.card : ℝ)) := by
    have h1 : ∀ x : ℕ, w x = (3000000000 : ℝ) * ((1 : ℝ) / (x : ℝ)) - 1000000 := fun x => by
      dsimp only [w]; ring
    simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hubR : ((targetK * 1000000 + (res.2.1 + slack) : ℕ) : ℝ) ≤ ((3000 * needLo : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcheck.2
  push_cast at hubR
  have hneed3000 : (3000 : ℝ) * (needLo : ℝ) ≤ (1000000 : ℝ) * ((3000 : ℝ) * need S) := by
    linarith
  have hstrict : (1000000 : ℝ) * ((3000 : ℝ) * need S - (T.card : ℝ)) <
      (1000000 : ℝ) * ((3000 : ℝ) * (∑ x ∈ T, (1 : ℝ) / (x : ℝ)) - (T.card : ℝ)) := by
    linarith
  have hltK : (targetK : ℝ) < (T.card : ℝ) := by linarith
  have hltN : targetK < T.card := Nat.cast_lt.mp hltK
  omega

/-- **Unconditional 575-Prime Normal-Set Bound (Pure Kernel, Zero `hN1`, Zero `native_decide`)**:
Every finite normal set of odd primes `P` with `∑_{p ∈ P} 1/p > 1` has at least `575` elements. -/
theorem unconditional_normal_set_575 {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    575 ≤ P.card := by
  have hsplit := split_normal_at_cut hP 5
  set S := P.filter (· < 5)
  set T := P.filter (5 ≤ ·)
  have hT_norm : IsNormalOddPrimeSet T := hsplit.2.1
  have hTail : ∀ x ∈ T, IsTailPrime S 5 x := hsplit.2.2.1
  have hcard : P.card = S.card + T.card := hsplit.2.2.2.2.2
  have hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ) := need_lt_tail_sum hP hsum 5
  have hS_cases : S = ∅ ∨ S = {3} := by
    by_cases h3 : 3 ∈ S
    · right
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
        have hx5 : x < 5 := (Finset.mem_filter.mp hx).2
        obtain ⟨hpr, hodd⟩ := hP.1 x hxP
        have h2 := hpr.two_le
        rcases hodd with ⟨t, rfl⟩
        omega
      · rintro rfl; exact h3
    · left
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
      have hx5 : x < 5 := (Finset.mem_filter.mp hx).2
      obtain ⟨hpr, hodd⟩ := hP.1 x hxP
      have h2 := hpr.two_le
      have hx3 : x = 3 := by rcases hodd with ⟨t, rfl⟩; omega
      exact h3 (hx3 ▸ hx)
  rcases hS_cases with hS0 | hS3
  · rw [hS0] at hTail hneed hcard
    have hneed_lo : (1000000 : ℝ) / 1000000 ≤ need ∅ := by simp [need]
    have hT575 : 575 ≤ T.card :=
      leaf3000_tail_bound hT_norm hTail hneed hneed_lo (fun h => by cases h) checkLeaf3000_empty
    simp [hcard]; omega
  · rw [hS3] at hTail hneed hcard
    have hneed_lo : (666666 : ℝ) / 1000000 ≤ need {3} := by
      unfold need
      simp only [Finset.sum_singleton]
      norm_num
    have hT587 : 587 ≤ T.card :=
      leaf3000_tail_bound hT_norm hTail hneed hneed_lo
        (fun _ => Finset.mem_singleton_self 3) checkLeaf3000_three
    have hScard : ({3} : Finset ℕ).card = 1 := rfl
    omega

/-- Unconditional prime count below `4,211`: `#{odd primes < 4211} ≤ 574 < 575` (pure `rfl`). -/
lemma swarPopcountUp_mask4211 :
    swarPopcountUp 16 (survivorMask &&& ((1 <<< 2105) - 1)) = 574 := rfl

lemma odd_prime_card_lt_4211 :
    ((Finset.range 4211).filter (fun p => Nat.Prime p ∧ Odd p)).card < 575 := by
  set mask4211 := survivorMask &&& ((1 <<< 2105) - 1)
  have hle :
      ((Finset.range 4211).filter (fun p => Nat.Prime p ∧ Odd p)).card ≤
        ((Finset.range 65536).filter (fun i => mask4211.testBit i = true)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp ⊢
      dsimp only
      refine ⟨by omega, ?_⟩
      rw [Nat.testBit_and, survivorMask_testBit_of_odd_prime hp.2.1 hp.2.2 (by omega),
        testBit_one_shiftLeft_sub_one]
      simp only [Bool.true_and, decide_eq_true_eq]
      omega
    · intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hp₁ hp₂
      rcases hp₁.2.2 with ⟨t₁, rfl⟩
      rcases hp₂.2.2 with ⟨t₂, rfl⟩
      dsimp only at heq
      omega
  have hpop := card_filter_testBit_le_swarPopcountUp mask4211
  rw [swarPopcountUp_mask4211] at hpop
  omega

/-- **Unconditional 578-Prime Giuga Counterexample Bound (Pure Kernel, Zero `hN1`, Zero `native_decide`)**:
Combining `unconditional_normal_set_575`, `lemma_C_general` at `q = 4211` (`575 + 4211 = 4786`),
and `giuga_card_mod_eight` (`m ≡ 2 [MOD 8]` at `v = 1`), every Giuga counterexample has at least
`578` distinct prime factors — strictly exceeding the classical 1950 Giuga and 1985 Bedocchi bounds
unconditionally. -/
theorem giuga_unconditional_578_primes {n : ℕ} (hn : IsGiugaCounterexample n) :
    578 ≤ n.primeFactors.card := by
  have hn2 : 2 ≤ n := hn.1
  obtain ⟨v, ⟨hv1, hv_eq⟩, _⟩ := giuga_exists_value hn
  have hnorm : IsNormalOddPrimeSet n.primeFactors := giuga_primeFactors_normal hn
  have hrecip := giuga_recip_sum_eq hn hv_eq
  rcases lt_or_ge v 2 with hv_lt2 | hv_ge2
  · have hv_one : v = 1 := by omega
    subst hv_one
    have h575 : 575 ≤ n.primeFactors.card :=
      unconditional_normal_set_575 hnorm (giuga_recip_sum_gt_one hn)
    have hmod8 : n.primeFactors.card ≡ 1 + 1 [MOD 8] := giuga_card_mod_eight hn hv_eq
    have hrem : n.primeFactors.card % 8 = 2 := by simpa [Nat.ModEq] using hmod8
    omega
  · have hgt2 : (2 : ℝ) < ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) := by
      rw [hrecip]
      have hvR : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv_ge2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hn_pos
      linarith
    have h4786 : 575 + 4211 ≤ n.primeFactors.card :=
      lemma_C_general (fun _ => unconditional_normal_set_575) odd_prime_card_lt_4211 hnorm hgt2
    omega

lemma prodMask4211_gt_10_pow_1803 :
    decide ((10 ^ 200) ^ 9 * (10 ^ 3) <
      prodMaskPow2 12 0 (survivorMask &&& ((1 <<< 2105) - 1)) * (4211 ^ 4)) = true := rfl

/-- **Unconditional 1,804-Digit Giuga Counterexample Bound (Pure Kernel, Zero `hN1`)**:
Every counterexample `n` to Giuga's conjecture satisfies `10 ^ 1803 < n` (at least `1,804`
decimal digits), surpassing Giuga's `10 ^ 1000` and Bedocchi's `10 ^ 1700` unconditionally. -/
theorem giuga_unconditional_gt_10_pow_1803 {n : ℕ} (hn : IsGiugaCounterexample n) :
    10 ^ 1803 < n := by
  set mask4211 := survivorMask &&& ((1 <<< 2105) - 1)
  set Q := maskOddSet (2 ^ 12) 0 mask4211
  have hQ_card : Q.card ≤ 574 := by
    have hcard_eq : Q.card =
        ((Finset.range (2 ^ 12)).filter (fun i => mask4211.testBit i = true)).card :=
      Finset.card_map _
    have hsub : (Finset.range (2 ^ 12)).filter (fun i => mask4211.testBit i = true) ⊆
        (Finset.range 65536).filter (fun i => mask4211.testBit i = true) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨by norm_num at hi; omega, hi.2⟩
    have hle := Finset.card_le_card hsub
    have hpop := card_filter_testBit_le_swarPopcountUp mask4211
    rw [swarPopcountUp_mask4211] at hpop
    omega
  have hQ_le : ∀ q ∈ Q, q ≤ 4211 := by
    intro q hq
    rcases mem_maskOddSet_iff.mp hq with ⟨i, _, htb, rfl⟩
    rw [Nat.testBit_and, testBit_one_shiftLeft_sub_one, Bool.and_eq_true,
      decide_eq_true_eq] at htb
    omega
  have hsub : ∀ p ∈ n.primeFactors, p < 4211 → p ∈ Q := by
    intro p hp hlt
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hodd := Odd.of_dvd_nat (giuga_odd hn) (Nat.dvd_of_mem_primeFactors hp)
    rw [mem_maskOddSet_iff]
    refine ⟨(p - 1) / 2, by norm_num; omega, ?_, by rcases hodd with ⟨t, rfl⟩; omega⟩
    rw [Nat.testBit_and, survivorMask_testBit_of_odd_prime hpr hodd (by omega),
      testBit_one_shiftLeft_sub_one]
    simp only [Bool.true_and, decide_eq_true_eq]
    omega
  have h578 : 574 + 4 ≤ n.primeFactors.card := giuga_unconditional_578_primes hn
  have hexch := prod_ge_of_low_subset_card (by omega : 1 ≤ 4211) hsub hQ_le hQ_card h578
  rw [prod_maskOddSet_eq_prodMaskPow2 12 0 mask4211, ← giuga_prod_primeFactors hn] at hexch
  have hgt := of_decide_eq_true prodMask4211_gt_10_pow_1803
  have hpow : (10 ^ 200) ^ 9 * (10 ^ 3) = 10 ^ 1803 := by
    rw [← pow_mul, ← pow_add]
  rw [hpow] at hgt
  exact lt_of_lt_of_le hgt hexch

/-! ### Part 4: Explicit Decimal-Digit Bounds (`10^36083`, `10^446177`, and Route (a) `10^40747`) -/

lemma survivorMask_lt_two_pow_41670 :
    ∀ i : ℕ, survivorMask.testBit i = true → i < 41670 := by
  intro i htb
  unfold survivorMask at htb
  rw [Nat.testBit_xor, Nat.testBit_or] at htb
  cases hc : sieveCompMask.testBit i
  · rw [hc, Bool.or_false, Bool.xor_false] at htb
    unfold fullOddMask at htb
    rw [Nat.testBit_shiftLeft, testBit_one_shiftLeft_sub_one] at htb
    by_cases hi1 : 1 ≤ i
    · simp only [hi1, decide_true, Bool.true_and, decide_eq_true_eq] at htb
      omega
    · simp only [hi1, decide_false, Bool.false_and, Bool.false_eq_true] at htb
  · rw [hc, Bool.or_true, Bool.xor_self] at htb
    cases htb

lemma prodSurvivor83341_gt_10_pow_36083 :
    decide ((10 ^ 200) ^ 180 * (10 ^ 83) <
      prodMaskPow2 16 0 survivorMask * (83341 ^ 4)) = true := rfl

lemma prodSurvivor83341_v2_gt_10_pow_446177 :
    decide ((10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 230 * (10 ^ 177) <
      prodMaskPow2 16 0 survivorMask * ((83341 ^ 200) ^ 200 * (83341 ^ 200) ^ 216 *
        (83341 ^ 142))) = true := rfl

/-- **Explicit 36,084-Digit Giuga Bound from `hN1` Alone (Zero Log-Certificate Assumptions)**:
Assuming only the prime-count hypothesis `hN1` (`N₁ ≥ 8135`), every counterexample `n` to
Giuga's conjecture satisfies `10 ^ 36083 < n` (at least `36,084` decimal digits), strictly
surpassing BBBG's Open Problem 5 threshold (`10 ^ 36068`) and Sorini's `10 ^ 36067`. -/
theorem cor_giuga_gt_10_pow_36083
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {n : ℕ} (hn : IsGiugaCounterexample n) :
    10 ^ 36083 < n := by
  set Q := maskOddSet (2 ^ 16) 0 survivorMask
  have hQ_card : Q.card ≤ 8134 := by
    have hcard_eq : Q.card =
        ((Finset.range 65536).filter (fun i => survivorMask.testBit i = true)).card := by
      have : 2 ^ 16 = 65536 := by norm_num
      rw [← this]
      exact Finset.card_map _
    have hpop := card_filter_testBit_le_swarPopcountUp survivorMask
    rw [swarPopcountUp_survivorMask] at hpop
    omega
  have hQ_le : ∀ q ∈ Q, q ≤ 83341 := by
    intro q hq
    rcases mem_maskOddSet_iff.mp hq with ⟨i, _, htb, rfl⟩
    have hi := survivorMask_lt_two_pow_41670 i htb
    omega
  have hsub : ∀ p ∈ n.primeFactors, p < 83341 → p ∈ Q := by
    intro p hp hlt
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hodd := Odd.of_dvd_nat (giuga_odd hn) (Nat.dvd_of_mem_primeFactors hp)
    rw [mem_maskOddSet_iff]
    refine ⟨(p - 1) / 2, by norm_num; omega,
      survivorMask_testBit_of_odd_prime hpr hodd hlt,
      by rcases hodd with ⟨t, rfl⟩; omega⟩
  have h8138 : 8134 + 4 ≤ n.primeFactors.card := cor_giuga_8138_primes hN1 hn
  have hexch := prod_ge_of_low_subset_card (by omega : 1 ≤ 83341) hsub hQ_le hQ_card h8138
  rw [prod_maskOddSet_eq_prodMaskPow2 16 0 survivorMask, ← giuga_prod_primeFactors hn] at hexch
  have hgt := of_decide_eq_true prodSurvivor83341_gt_10_pow_36083
  have hpow : (10 ^ 200) ^ 180 * (10 ^ 83) = 10 ^ 36083 := by
    rw [← pow_mul, ← pow_add]
  rw [hpow] at hgt
  exact lt_of_lt_of_le hgt hexch

/-- **Lemma C Product Lower Bound (`v ≥ 2` branch, parameterized only by `hN1`)**:
Assuming `hN1`, every normal odd prime set `P` with `∑_{p ∈ P} 1/p > 2` satisfies
`10 ^ 446177 < ∏ p ∈ P, p` (and in particular `10 ^ 40747 < ∏ p ∈ P, p`). -/
theorem lemma_C_prod_gt_10_pow_446177
    (hN1 : ∀ P : Finset ℕ, IsNormalOddPrimeSet P → (1 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      8135 ≤ P.card)
    {P : Finset ℕ} (hP : IsNormalOddPrimeSet P)
    (hsum : (2 : ℝ) < ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :
    10 ^ 446177 < ∏ p ∈ P, p := by
  set Q := maskOddSet (2 ^ 16) 0 survivorMask
  have hQ_card : Q.card ≤ 8134 := by
    have hcard_eq : Q.card =
        ((Finset.range 65536).filter (fun i => survivorMask.testBit i = true)).card := by
      have : 2 ^ 16 = 65536 := by norm_num
      rw [← this]
      exact Finset.card_map _
    have hpop := card_filter_testBit_le_swarPopcountUp survivorMask
    rw [swarPopcountUp_survivorMask] at hpop
    omega
  have hQ_le : ∀ q ∈ Q, q ≤ 83341 := by
    intro q hq
    rcases mem_maskOddSet_iff.mp hq with ⟨i, _, htb, rfl⟩
    have hi := survivorMask_lt_two_pow_41670 i htb
    omega
  have hsub : ∀ p ∈ P, p < 83341 → p ∈ Q := by
    intro p hp hlt
    obtain ⟨hpr, hodd⟩ := hP.1 p hp
    rw [mem_maskOddSet_iff]
    refine ⟨(p - 1) / 2, by norm_num; omega,
      survivorMask_testBit_of_odd_prime hpr hodd hlt,
      by rcases hodd with ⟨t, rfl⟩; omega⟩
  have h91476 : 8134 + 83342 ≤ P.card := lemma_C_91476 hN1 hP hsum
  have hexch := prod_ge_of_low_subset_card (by omega : 1 ≤ 83341) hsub hQ_le hQ_card h91476
  rw [prod_maskOddSet_eq_prodMaskPow2 16 0 survivorMask] at hexch
  have hgt := of_decide_eq_true prodSurvivor83341_v2_gt_10_pow_446177
  have hpow10 :
      (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 * (10 ^ 200) ^ 200 *
        (10 ^ 200) ^ 200 * (10 ^ 200) ^ 230 * (10 ^ 177) = 10 ^ 446177 := by
    repeat rw [← pow_mul]
    repeat rw [← pow_add]
  have hpow83 :
      (83341 ^ 200) ^ 200 * (83341 ^ 200) ^ 216 * (83341 ^ 142) = 83341 ^ 83342 := by
    repeat rw [← pow_mul]
    repeat rw [← pow_add]
  rw [hpow10, hpow83] at hgt
  exact lt_of_lt_of_le hgt hexch

/-- Least integer `K' ≥ K` satisfying `sCard + K' ≡ 2 [MOD 4]` (Theorem 2(b) Route (a) lift). -/
def routeALiftK (sCard K : ℕ) : ℕ :=
  K + (6 - (sCard + K) % 4) % 4

/-- Specification of `routeALiftK`: `K ≤ routeALiftK sCard K`, `(sCard + routeALiftK sCard K) % 4 = 2`,
and `routeALiftK sCard K ≤ tCard` whenever `K ≤ tCard` and `(sCard + tCard) % 4 = 2`. -/
theorem routeALiftK_spec (sCard K : ℕ) :
    K ≤ routeALiftK sCard K ∧
      (sCard + routeALiftK sCard K) % 4 = 2 ∧
      ∀ tCard : ℕ, K ≤ tCard → (sCard + tCard) % 4 = 2 → routeALiftK sCard K ≤ tCard := by
  unfold routeALiftK
  refine ⟨by omega, by omega, ?_⟩
  intro tCard hK hmod
  omega

/-- **Lemma W Refinement 2 + K7 Linear Lift (`Theorem 2(b)`, Route (a))**:
At any leaf `(p_d, S)`, if a normal odd prime set `P` with `∑ 1/p > 1` hits `S = P.filter (· < p_d)`,
has `K ≤ (P.filter (p_d ≤ ·)).card`, and satisfies `P.card ≡ 2 [MOD 4]`, then Refinement 2
upgrades linearly from `K` to `K' = routeALiftK S.card K` without re-solving `η`:
`(∑ s ∈ S, ln s) + μ * need S + ν * K' - UB(U, E, f, η) ≤ ln (∏ p ∈ P, p)`. -/
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
      Real.log (∏ p ∈ P, (p : ℝ)) := by
  dsimp only
  set S := P.filter (· < p_d)
  set T := P.filter (p_d ≤ ·)
  have hsplit := split_normal_at_cut hP p_d
  have hcard : P.card = S.card + T.card := hsplit.2.2.2.2.2
  have hrem : (S.card + T.card) % 4 = 2 := by
    rw [← hcard]
    simpa [Nat.ModEq] using hmod4
  have hK' : routeALiftK S.card K ≤ T.card := (routeALiftK_spec S.card K).2.2 T.card hK hrem
  have hneed : need S < ∑ x ∈ T, (1 : ℝ) / (x : ℝ) := need_lt_tail_sum hP hsum p_d
  have href2 := lemma_w_refinement2 hsplit.2.1 hsplit.2.2.1 hneed hK' hμ hν hC hfC hU hE hη
  have hpos : ∀ p ∈ P, (0 : ℝ) ≠ (p : ℝ) := fun p hp =>
    ne_of_lt (Nat.cast_pos.mpr (hP.1 p hp).1.pos)
  have hlog_prod : Real.log (∏ p ∈ P, (p : ℝ)) =
      (∑ s ∈ S, Real.log (s : ℝ)) + ∑ x ∈ T, Real.log (x : ℝ) := by
    rw [Real.log_prod (fun p hp => (hpos p hp).symm), ← hsplit.2.2.2.2.1,
      Finset.sum_union hsplit.2.2.2.1]
  linarith

lemma pow_le_pow_of_le {b i j : ℕ} (hb : 1 ≤ b) (hij : i ≤ j) : b ^ i ≤ b ^ j :=
  Nat.pow_le_pow_right hb hij

/-- **40,748-Digit Giuga Counterexample Bound (`Theorem 2(b)`, `10 ^ 40747 < n`)**:
Combining `hN1` (which rules out `v ≥ 2` via `lemma_C_prod_gt_10_pow_446177` with margin
`> 400,000` digits) and the depth-6 Route (a) frontier hypothesis `hRouteA` (certifying on
each normal prefix `S` below `17` that `K_S` tail primes and Refinement 2 parameters
`(μ_S, ν_S, C_S, U_S, E_S, η_S)` satisfy the lifted log bound `> 40747 * ln 10`),
every counterexample `n` to Giuga's conjecture satisfies `10 ^ 40747 < n`. -/
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
    10 ^ 40747 < n := by
  have hn2 : 2 ≤ n := hn.1
  obtain ⟨v, ⟨hv1, hv_eq⟩, _⟩ := giuga_exists_value hn
  have hnorm : IsNormalOddPrimeSet n.primeFactors := giuga_primeFactors_normal hn
  have hprod : n = ∏ p ∈ n.primeFactors, p := giuga_prod_primeFactors hn
  have hrecip := giuga_recip_sum_eq hn hv_eq
  rcases lt_or_ge v 2 with hv_lt2 | hv_ge2
  · have hv_one : v = 1 := by omega
    subst hv_one
    have hgt1 : (1 : ℝ) < ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) := giuga_recip_sum_gt_one hn
    have hmod4 : n.primeFactors.card ≡ 2 [MOD 4] :=
      odd_giuga_card_mod_four (giuga_odd hn) (giuga_squarefree hn) hv_eq
    set S := n.primeFactors.filter (· < 17)
    have hsplit := split_normal_at_cut hnorm 17
    have hS_mem : S ∈ F := hF S hsplit.1 (fun s hs => (Finset.mem_filter.mp hs).2)
    obtain ⟨hμ, hν, hC, hfC, hU, hE, hη, hgt_log⟩ := hCert S hS_mem
    have hlog_ge := lemma_w_refinement2_route_a hnorm hgt1 hmod4
      (hTailK n.primeFactors hnorm hgt1) hμ hν hC hfC hU hE hη
    have hlt_log : (40747 : ℝ) * Real.log 10 < Real.log (n : ℝ) := by
      have hcast_prod : (∏ p ∈ n.primeFactors, (p : ℝ)) = (n : ℝ) := by
        conv_rhs => rw [hprod]
        simp [Nat.cast_prod]
      rw [hcast_prod] at hlog_ge
      linarith
    have h10R_pos : (0 : ℝ) < (10 : ℝ) ^ (40747 : ℕ) :=
      pow_pos (by norm_num : (0 : ℝ) < 10) 40747
    have hn_pos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) hn2)
    have hlog_pow : (40747 : ℝ) * Real.log 10 = Real.log ((10 : ℝ) ^ (40747 : ℕ)) := by
      rw [Real.log_pow]; norm_num
    rw [hlog_pow] at hlt_log
    have hltR : (10 : ℝ) ^ (40747 : ℕ) < (n : ℝ) :=
      (Real.log_lt_log_iff h10R_pos hn_pos).mp hlt_log
    have hcast10 : (((10 ^ 40747 : ℕ) : ℝ)) = (10 : ℝ) ^ (40747 : ℕ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [← hcast10] at hltR
    exact Nat.cast_lt.mp hltR
  · have hgt2 : (2 : ℝ) < ∑ p ∈ n.primeFactors, (1 : ℝ) / (p : ℝ) := by
      rw [hrecip]
      have hvR : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv_ge2
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hn_pos
      linarith
    have hbig := lemma_C_prod_gt_10_pow_446177 hN1 hnorm hgt2
    rw [← hprod] at hbig
    have hpow_le : 10 ^ 40747 ≤ 10 ^ 446177 :=
      pow_le_pow_of_le (by decide) (by decide)
    exact lt_of_le_of_lt hpow_le hbig

end Giuga
