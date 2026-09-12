import Spider

/-!
# Certificate

Printing the axioms used by the headline theorems. A sound, `sorry`-free development uses only
the three standard axioms of Lean's kernel: `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms Spider.main
#print axioms Spider.spider_isContained
#print axioms Spider.edge_bound
#print axioms Spider.edge_bound_of_colorable
#print axioms Spider.exbip_le
#print axioms Spider.spider_free_K44
#print axioms Spider.exbip_four_four
#print axioms Spider.spider_free_qK44
#print axioms Spider.card_edgeFinset_qK44
#print axioms Spider.exbip_eq_of_qK44
#print axioms Spider.spider_free_gapGraph
#print axioms Spider.card_edgeFinset_gapGraph
#print axioms Spider.exbip_ge
#print axioms Spider.exbip_within_eight
#print axioms Spider.card_leaves_add
#print axioms Spider.sigma_lower
#print axioms Spider.census
#print axioms Spider.spider_isTree
#print axioms Spider.spider_outside_criterion
#print axioms Spider.corollary_nine
#print axioms Spider.corollary_nine_order
