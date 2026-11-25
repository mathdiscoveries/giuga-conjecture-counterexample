module

public import Giuga

/-!
# Axiom Verification Audit for `Giuga`

Prints the Lean 4 kernel axioms used by every public theorem and lemma across all five
modules of `Giuga` (`128` declarations total). A clean audit must show ONLY Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) — NEVER `sorryAx`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, or any custom axiom.
-/

-- Module 1: Definitions and classical reductions K1, K2, K3, K7 (Defs.lean)
#print axioms Giuga.IsNormalOddPrimeSet.subset
#print axioms Giuga.IsNormalOddPrimeSet.not_dvd_sub_one
#print axioms Giuga.sum_Ico_one_eq_sum_range
#print axioms Giuga.prime_pow_sum_zmod
#print axioms Giuga.pow_sum_zmod_of_dvd
#print axioms Giuga.sub_one_dvd_sub_one_iff
#print axioms Giuga.squarefree_of_giuga_condition
#print axioms Giuga.modEq_prod_of_forall_mem
#print axioms Giuga.giuga_iff_carmichael_and_giuga
#print axioms Giuga.giuga_squarefree
#print axioms Giuga.giuga_prod_primeFactors
#print axioms Giuga.giuga_two_le_card
#print axioms Giuga.giuga_odd
#print axioms Giuga.giuga_primeFactors_normal
#print axioms Giuga.prod_dvd_of_forall_dvd
#print axioms Giuga.giuga_exists_value
#print axioms Giuga.giuga_recip_sum_eq
#print axioms Giuga.giuga_recip_sum_gt_one
#print axioms Giuga.odd_sq_zmod4
#print axioms Giuga.two_mul_add_neg_one_pow_zmod4
#print axioms Giuga.odd_giuga_card_mod_four

-- Module 2: Lemma W, Frontier, Refinements 1 & 2, and Hand Case (LemmaW.lean)
#print axioms Giuga.empty_mem_indepPowerset
#print axioms Giuga.le_mwis
#print axioms Giuga.zero_le_mwis
#print axioms Giuga.normal_isIndependent
#print axioms Giuga.split_normal_at_cut
#print axioms Giuga.need_lt_tail_sum
#print axioms Giuga.edge_dual_le_ub_of_independent
#print axioms Giuga.edge_dual_le_ub
#print axioms Giuga.sum_le_sum_inter_of_nonpos
#print axioms Giuga.lemma_w_forest_count
#print axioms Giuga.lemma_w_forest_prod
#print axioms Giuga.lemma_w_edge_dual_count
#print axioms Giuga.lemma_w_edge_dual_prod
#print axioms Giuga.exists_unique_leaf_in_frontier
#print axioms Giuga.lemma_w_frontier_count
#print axioms Giuga.lemma_w_refinement1
#print axioms Giuga.lemma_w_refinement1_scaling
#print axioms Giuga.refinement2_weight_nonpos
#print axioms Giuga.lemma_w_refinement2
#print axioms Giuga.lemma_w_refinement2_strict
#print axioms Giuga.hand_case_nine_primes
#print axioms Giuga.giuga_nine_primes

-- Module 3: Lemma C, 8,135th odd prime sieve, 8,138-Prime Corollary, and Section 4 Rules (CeilingAndRules.lean)
#print axioms Giuga.lemma_C_general
#print axioms Giuga.testBit_eq_decide_div_mod
#print axioms Giuga.periodicMask_mul_eq
#print axioms Giuga.testBit_periodicMask_dvd
#print axioms Giuga.not_prime_of_testBit_sieveRow
#print axioms Giuga.foldl_sieve_sound
#print axioms Giuga.smallOddPrimes_valid
#print axioms Giuga.testBit_fullMask_shifted
#print axioms Giuga.survivorMask_testBit_of_odd_prime
#print axioms Giuga.testBit_altMaskAux
#print axioms Giuga.add_div_pow_mod_of_no_carry
#print axioms Giuga.block_and_altMaskAux
#print axioms Giuga.fieldSum_swarStep
#print axioms Giuga.fieldSum_swarPopcountUp
#print axioms Giuga.card_filter_testBit_le_swarPopcountUp
#print axioms Giuga.swarPopcountUp_survivorMask
#print axioms Giuga.odd_prime_card_lt_83341
#print axioms Giuga.odd_prime_8135_ge_83341
#print axioms Giuga.lemma_C_91476
#print axioms Giuga.cor_giuga_8138_primes
#print axioms Giuga.prod_offDiag_eq_prod_lt
#print axioms Giuga.card_filter_lt_prod
#print axioms Giuga.giuga_reciprocity_rule
#print axioms Giuga.odd_sq_zmod8
#print axioms Giuga.giuga_residue_mod_8
#print axioms Giuga.giuga_exactness_rule

-- Module 4: Mod-8 Count Rule, Unconditional 578-Prime / 1,804-Digit Bounds, and Explicit Digit Corollaries (UnconditionalAndDigits.lean)
#print axioms Giuga.odd_four_mul_zmod8
#print axioms Giuga.odd_prod_of_forall_odd
#print axioms Giuga.two_mul_prod_odd_zmod8
#print axioms Giuga.choose_two_succ
#print axioms Giuga.sum_sub_prod_odd_zmod8
#print axioms Giuga.giuga_card_mod_eight
#print axioms Giuga.testBit_one_shiftLeft_sub_one
#print axioms Giuga.mem_maskOddSet_iff
#print axioms Giuga.maskOddSet_pow2_split
#print axioms Giuga.testBit_zero_eq_and_one
#print axioms Giuga.prod_maskOddSet_eq_prodMaskPow2
#print axioms Giuga.prod_ge_of_low_subset_card
#print axioms Giuga.Trie.wf_zero
#print axioms Giuga.Trie.get_zero
#print axioms Giuga.Trie.wf_singleton
#print axioms Giuga.Trie.wf_merge
#print axioms Giuga.Trie.get_singleton
#print axioms Giuga.Trie.get_merge
#print axioms Giuga.evalEdgesPow2_sound
#print axioms Giuga.sum_maskOddSet_slack_eq
#print axioms Giuga.checkLeaf3000_empty
#print axioms Giuga.checkLeaf3000_three
#print axioms Giuga.leaf3000_tail_bound
#print axioms Giuga.unconditional_normal_set_575
#print axioms Giuga.swarPopcountUp_mask4211
#print axioms Giuga.odd_prime_card_lt_4211
#print axioms Giuga.giuga_unconditional_578_primes
#print axioms Giuga.prodMask4211_gt_10_pow_1803
#print axioms Giuga.giuga_unconditional_gt_10_pow_1803
#print axioms Giuga.survivorMask_lt_two_pow_41670
#print axioms Giuga.prodSurvivor83341_gt_10_pow_36083
#print axioms Giuga.prodSurvivor83341_v2_gt_10_pow_446177
#print axioms Giuga.cor_giuga_gt_10_pow_36083
#print axioms Giuga.lemma_C_prod_gt_10_pow_446177
#print axioms Giuga.routeALiftK_spec
#print axioms Giuga.lemma_w_refinement2_route_a
#print axioms Giuga.pow_le_pow_of_le
#print axioms Giuga.cor_giuga_route_a_gt_10_pow_40747

-- Module 5: Unconditional 8,135-Prime Normal Witness & 8,138-Prime 7-Rule Ceiling Witness (Witness8135.lean)
#print axioms Giuga.testBit_periodicMask_of_lt
#print axioms Giuga.multsMask_eq_shift
#print axioms Giuga.testBit_multsMask_of_lt
#print axioms Giuga.foldl_or_mono
#print axioms Giuga.foldl_or_of_mem
#print axioms Giuga.allRangePow2_sound
#print axioms Giuga.allRange_checkSmallOdd569
#print axioms Giuga.mem_smallOddPrimes102_of_odd_prime
#print axioms Giuga.minFac_sq_le_of_not_prime
#print axioms Giuga.prime_of_sieveComp321145_false
#print axioms Giuga.allRange_checkTrial1999993
#print axioms Giuga.prime_1999993
#print axioms Giuga.evalPacked_sound
#print axioms Giuga.checkWitnessBundle_eq_true
#print axioms Giuga.testBit_zero_of_and_eq_zero
#print axioms Giuga.bundle_extract
#print axioms Giuga.greedySet8135_spec
#print axioms Giuga.exists_normal_odd_prime_set_8135
#print axioms Giuga.normal_odd_prime_min_eq_8135
#print axioms Giuga.ceilingWitness8138_spec
#print axioms Giuga.exists_ceiling_witness_8138
