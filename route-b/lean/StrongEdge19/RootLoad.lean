module

public import StrongEdge19.Root19

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The original type load and full conflict degree share the same budget. -/
theorem root_label_load_add_degree_le_twenty_four
    (hΔ : ∀ x, G.degree x ≤ 4) {r a : V}
    (hN : G.IsIndepSet (G.neighborSet r))
    (e : G.edgeSet) (he : e.val = s(r, a)) :
    (∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card) +
      (conflictGraph G).degree e ≤ 24 := by
  have hra := G.mem_edgeSet.mp (he ▸ e.property)
  have hdis : Disjoint ((G.neighborFinset r).erase a) ((G.neighborFinset a).erase r) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hN hra ((G.mem_neighborFinset r x).mp (mem_erase.mp hx).2) (mem_erase.mp hx).1.symm
      ((G.mem_neighborFinset a x).mp (mem_erase.mp hy).2)
  rw [← fourCycleOpposites_card_eq_root_load]
  have hc : (fourCycleOpposites G r a).card ≤
      (edgesInside G univ (endpointNeighbourCover G r a)).card := by
    apply card_le_via_relation _ _ (fun p f => f.val = s(p.1, p.2))
    · intro p hp
      obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp hp
      refine ⟨⟨s(p.1, p.2), hpAdj⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact Sym2.forall_mem_pair.mpr ⟨mem_union_left _ hx, mem_union_right _ hy⟩
    · intro p hp q hq f hpf hqf
      obtain ⟨hp, _⟩ := mem_filter.mp hp
      obtain ⟨hq, _⟩ := mem_filter.mp hq
      obtain ⟨hxp, _⟩ := mem_product.mp hp
      obtain ⟨_, hyq⟩ := mem_product.mp hq
      rcases Sym2.eq_iff.mp (hpf.symm.trans hqf) with h | h
      · exact Prod.ext h.1 h.2
      · exact (disjoint_left.mp hdis hxp (h.1.symm ▸ hyq)).elim
  have hi := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G r a) (fun x _ => hΔ x)
  have hb := endpointNeighbourCover_card_le_six G hra hΔ
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high19_root_label_budget_five
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e)
    {r a : V} (hN : G.IsIndepSet (G.neighborSet r)) (ha : a ∈ rootLabels G Q r) :
    (∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card) ≤ 5 := by
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp ha
  have hl := root_label_load_add_degree_le_twenty_four G hΔ hN e he
  have hd := h19 e heQ
  omega

omit [DecidableRel (conflictGraph G).Adj] in
/-- Three triples on at most four root labels have a common original label. -/
theorem three_triple_types_share_label
    (hΔ : ∀ x, G.degree x ≤ 4) {r x y z : V}
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (hz : 3 ≤ (rootType G r z).card) :
    ∃ a, a ∈ rootType G r x ∧ a ∈ rootType G r y ∧ a ∈ rootType G r z := by
  have hu : (rootType G r x ∪ rootType G r y).card ≤ 4 := by
    apply le_trans (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _)))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hΔ r
  have hi := card_union_add_card_inter (rootType G r x) (rootType G r y)
  have hu' : ((rootType G r x ∩ rootType G r y) ∪ rootType G r z).card ≤ 4 := by
    apply le_trans (card_le_card (union_subset
      (Subset.trans inter_subset_left (filter_subset _ _)) (filter_subset _ _)))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hΔ r
  have hi' := card_union_add_card_inter (rootType G r x ∩ rootType G r y) (rootType G r z)
  obtain ⟨a, ha⟩ := card_pos.mp
    (show 0 < ((rootType G r x ∩ rootType G r y) ∩ rootType G r z).card by omega)
  exact ⟨a, (mem_inter.mp (mem_inter.mp ha).1).1,
    (mem_inter.mp (mem_inter.mp ha).1).2, (mem_inter.mp ha).2⟩

/-- At full conflict degree nineteen, three distinct original triple tips are impossible. -/
theorem high19_no_three_triple_types
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hfull : rootLabels G Q r = G.neighborFinset r)
    {x y z : V} (hxr : x ≠ r) (hyr : y ≠ r) (hzr : z ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (hz : 3 ≤ (rootType G r z).card) : False := by
  obtain ⟨a, hax, hay, haz⟩ := three_triple_types_share_label G hΔ hx hy hz
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ hax
  have hb := high19_root_label_budget_five G hΔ Q h19 hN haR
  let N := (G.neighborFinset a).erase r
  have hxN : x ∈ N := mem_erase.mpr ⟨hxr,
    (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hyN : y ∈ N := mem_erase.mpr ⟨hyr,
    (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
  have hzN : z ∈ N := mem_erase.mpr ⟨hzr,
    (G.mem_neighborFinset a z).mpr ((mem_rootType G r z a).mp haz).2.symm⟩
  have hs : ({x, y, z} : Finset V) ⊆ N := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun w => ((rootType G r w).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  have hxn : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  rw [sum_insert hxn, sum_pair hyz] at hsum
  have hcx := card_erase_add_one hax
  have hcy := card_erase_add_one hay
  have hcz := card_erase_add_one haz
  change _ ≤ ∑ w ∈ (G.neighborFinset a).erase r, _ at hsum
  omega

end StrongEdge19
