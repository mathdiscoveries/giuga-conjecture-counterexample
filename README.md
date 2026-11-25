# How Many Prime Factors Could a Counterexample to Giuga's Conjecture Have? (`Giuga`)

Lean 4 (`v4.35.0`) + Mathlib formalization of structural reductions, edge-dual
linear-programming relaxations (Lemma W and refinements), Lemma C, local
obstruction rules, unconditional counterexample lower bounds, explicit ceiling
witnesses, and conditional transfer theorems for Giuga's primality conjecture
($\sum_{k=1}^{n-1} k^{n-1} \equiv -1 \pmod n$ for composite $n \ge 2$).

**Verification Scope (Partial Lean 4 + External Exact-Integer Certificates):**
Main results in the companion paper: 0 of 2 headline theorems purely in Lean 4
(0%) · 2 of 2 by Lean 4 + external exact-integer certificates across all 15
normal prefixes below $17$. Existence of a composite counterexample remains
open. All 21 compared theorems in `Challenge.lean` / `Solution.lean` (and all
128 declarations audited in `Giuga/Verify.lean`) build in Lean 4 + Mathlib with
zero `sorry`, zero `native_decide`, and Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) only.

## Formalized Headline Results (`Challenge.lean` / `Solution.lean`)

1. **Unconditional counterexample lower bounds (zero external hypotheses):**
   - `unconditional_normal_set_575`: every finite normal odd prime set $P$ with
     $\sum_{p \in P} 1/p > 1$ satisfies $|P| \ge 575$.
   - `giuga_unconditional_578_primes`: every Giuga counterexample $n$ has at
     least $578$ distinct prime factors.
   - `giuga_unconditional_gt_10_pow_1803`: every Giuga counterexample satisfies
     $n > 10^{1803}$ (at least $1{,}804$ decimal digits).
2. **Unconditional ceiling witnesses (pure-kernel exact witnesses):**
   - `exists_normal_odd_prime_set_8135`: exhibits an explicit $8{,}135$-element
     normal odd prime set $G$ with $\sum_{p \in G} 1/p > 1$ (over $\mathbb{Q}$
     and $\mathbb{R}$) and $10^{40732} < \prod_{p \in G} p < 10^{40733}$
     ($40{,}733$ decimal digits).
   - `exists_ceiling_witness_8138`: exhibits an explicit $8{,}138$-element
     normal odd prime set $W$ with $3 \notin W$ satisfying all seven local
     Giuga counterexample rules simultaneously (oddness, normality,
     $\sum 1/p > 1$, exactness $\sum_{q \in W \setminus \{p\}} 1/q \le 1$,
     quadratic-reciprocity count $k_3 \bmod 4 \in \{0, 1\}$, mod-8 residue
     $\sum p \equiv 1 + \prod p \pmod 8$, and $|W| = 8{,}138 \equiv 2 \pmod 8$)
     with $10^{40750} < \prod_{p \in W} p < 10^{40751}$ ($40{,}751$ decimal
     digits).
3. **Unconditional Lemma W, Lemma C, and 8,135th odd prime lower bound:**
   - `lemma_w_edge_dual_count`, `lemma_w_edge_dual_prod`,
     `lemma_w_frontier_count`, `lemma_w_refinement2_strict`,
     `lemma_w_refinement2_route_a`: edge-dual LP relaxations over the tail
     conflict graph ($q \mid r - 1$), complete frontier aggregation, strict
     Refinement 2 log bound, and Route (a) modulo-4 linear lift.
   - `lemma_C_general`, `odd_prime_8135_ge_83341`: general threshold-2 lift
     ($N_1 + q \le |P|$) and unconditional 60-prime GMP bitmask sieve + SWAR
     popcount proving every set of $\ge 8{,}135$ odd primes contains a prime
     $\ge 83{,}341$.
4. **Unconditional local obstruction rules:**
   - `giuga_reciprocity_rule` ($k_3 \bmod 4 \in \{0, 1\}$),
     `giuga_residue_mod_8` ($\sum p \equiv v + n \pmod 8$),
     `giuga_exactness_rule` (at $v = 1$, $(\sum 1/q) - 1 < 1/p$), and
     `giuga_card_mod_eight` ($|P| \equiv v + 1 \pmod 8$, proved elementarily
     via the mod-8 sum-product identity and quadratic reciprocity).
5. **Explicitly parameterized conditional transfer theorems:**
   - `lemma_C_91476`, `cor_giuga_8138_primes`, `cor_giuga_gt_10_pow_36083`,
     `lemma_C_prod_gt_10_pow_446177`: taking only `hN1` ($N_1 \ge 8{,}135$)
     explicitly, deduce $\ge 91{,}476$ primes and $> 10^{446177}$ for $v \ge 2$,
     $\ge 8{,}138$ distinct prime factors, and $n > 10^{36083}$ ($\ge 36{,}084$
     digits, with zero external log-certificate hypotheses).
   - `cor_giuga_route_a_gt_10_pow_40747`: taking `hN1` and the depth-6
     Route (a) frontier certificate hypotheses explicitly, deduces
     $n > 10^{40747}$ ($\ge 40{,}748$ decimal digits).

## Scope & Companion Artifacts

The 15-leaf depth-6 exact-integer dual certificates discharging `hN1`
($N_1 \ge 8{,}135$) and the Route (a) frontier ($n > 10^{40747}$) are checked
externally in deterministic exact integer arithmetic rather than inside Lean 4.
The companion working paper, exact integer checker, edge certificate archive,
and prior-work search logs live at https://mathdiscoveries.org/results/giuga.

## Local Verification

```sh
lake build Challenge Solution Giuga
lake env lean Giuga/Verify.lean
lake comparator --inadvisably-no-sandbox --config comparator.json
```

## Disclosure & License

Generated and checked by AI research agents built and directed by **Tyler B.
Hughes**. No human mathematician has yet refereed the proof. Licensed under
Apache-2.0 (see `LICENSE`).
