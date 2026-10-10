module

public import StrongEdge19.RootLoad

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem selected_tip_adj_full_double_of_missing_label
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r a x y : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hx : x ∈ fullDoubleTips G Q r)
    (hty : (rootType G r y).card ≤ 2) (hxa : a ∉ rootType G r x)
    (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(a, y)) : G.Adj y x := by
  have hya : a ∈ rootType G r y := (mem_rootType G r y a).mpr
    ⟨ha, (G.mem_edgeSet.mp (he ▸ e.property)).symm⟩
  have hnsub : ¬ rootType G r x ⊆ rootType G r y := by
    intro hs
    have hs' : rootType G r x ⊆ (rootType G r y).erase a :=
      fun b hb => mem_erase.mpr ⟨fun h => hxa (h ▸ hb), hs hb⟩
    have hc := card_le_card hs'
    have hec := card_erase_add_one hya
    have hcx := (mem_filter.mp hx).2.2.1
    omega
  obtain ⟨b, hbx, hby⟩ := not_subset.mp hnsub
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp ((mem_filter.mp hx).2.2.2 hbx)
  exact root_selected_edges_force_adj G Q hQ hN ha
    ((mem_rootType G r x b).mp hbx).1 hby hxa e f heQ hfQ he (hf.trans Sym2.eq_swap)

theorem rootTips_card_le_four_of_disjoint_full_double_types
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r x y : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ w, w ≠ r → (rootType G r w).card ≤ 2)
    (hx : x ∈ fullDoubleTips G Q r) (hy : y ∈ fullDoubleTips G Q r)
    (hdis : Disjoint (rootType G r x) (rootType G r y)) :
    (rootTips G Q r).card ≤ 4 := by
  have hs : rootTips G Q r ⊆ (G.neighborFinset x \ G.neighborFinset r) ∪
      (G.neighborFinset y \ G.neighborFinset r) := by
    intro w hw
    obtain ⟨_, hwr, a, haN, e, heQ, he⟩ := mem_filter.mp hw
    have ha := (G.mem_neighborFinset r a).mp haN
    have hn : w ∉ G.neighborFinset r := fun h =>
      root_edge_tip_not_neighbor G hN ha e he ((G.mem_neighborFinset r w).mp h)
    by_cases hax : a ∈ rootType G r x
    · have hay : a ∉ rootType G r y := fun h => disjoint_left.mp hdis hax h
      exact mem_union_right _ (mem_sdiff.mpr ⟨(G.mem_neighborFinset y w).mpr
        (selected_tip_adj_full_double_of_missing_label G Q hQ hN ha hy (ht w hwr) hay e heQ he).symm, hn⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨(G.mem_neighborFinset x w).mpr
        (selected_tip_adj_full_double_of_missing_label G Q hQ hN ha hx (ht w hwr) hax e heQ he).symm, hn⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have htx := (mem_filter.mp hx).2.2.1
  have hty := (mem_filter.mp hy).2.2.1
  have hrx := residual_neighbors_add_type_card G r x
  have hry := residual_neighbors_add_type_card G r y
  have hdx := hΔ x
  have hdy := hΔ y
  omega

theorem rootTips_card_le_five_of_three_equal_full_double_types
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r x : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ w, w ≠ r → (rootType G r w).card ≤ 2)
    (hx : x ∈ fullDoubleTips G Q r)
    (hthree : (fullDoubleTips G Q r).card = 3)
    (hequal : ∀ y ∈ fullDoubleTips G Q r, rootType G r y = rootType G r x) :
    (rootTips G Q r).card ≤ 5 := by
  let D := fullDoubleTips G Q r
  have hs : rootTips G Q r ⊆ D ∪ (G.neighborFinset x \ G.neighborFinset r) := by
    intro w hw
    by_cases hwD : w ∈ D
    · exact mem_union_left _ hwD
    obtain ⟨_, hwr, a, haN, e, heQ, he⟩ := mem_filter.mp hw
    have ha := (G.mem_neighborFinset r a).mp haN
    have haw : G.Adj a w := G.mem_edgeSet.mp (he ▸ e.property)
    have hax : a ∉ rootType G r x := by
      intro hax
      have hsub : D ⊆ (G.neighborFinset a).erase r := by
        intro y hy
        have hay : a ∈ rootType G r y := (hequal y hy).symm ▸ hax
        exact mem_erase.mpr ⟨(mem_filter.mp hy).2.1,
          (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
      have hec := card_erase_add_one ((G.mem_neighborFinset a r).mpr ha.symm)
      have hda := hΔ a
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hec
      have heq : D = (G.neighborFinset a).erase r := eq_of_subset_of_card_le hsub (by
        change D.card = 3 at hthree
        omega)
      exact hwD (heq.symm ▸ mem_erase.mpr ⟨hwr, (G.mem_neighborFinset a w).mpr haw⟩)
    have hn : w ∉ G.neighborFinset r := fun h =>
      root_edge_tip_not_neighbor G hN ha e he ((G.mem_neighborFinset r w).mp h)
    exact mem_union_right _ (mem_sdiff.mpr ⟨(G.mem_neighborFinset x w).mpr
      (selected_tip_adj_full_double_of_missing_label G Q hQ hN ha hx (ht w hwr) hax e heQ he).symm, hn⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have htx := (mem_filter.mp hx).2.2.1
  have hrx := residual_neighbors_add_type_card G r x
  have hdx := hΔ x
  change D.card = 3 at hthree
  omega

variable [DecidableRel (conflictGraph G).Adj]

/-- The missing high21 small-type improvement: at most eight selected type edges. -/
theorem high21_small_types_rootEdges_card_le_eight
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r : V} (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) :
    (rootEdges G Q r).card ≤ 8 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high21_root_neighborhood_independent G hΔ Q h21 r (by omega)
  have hp := high21_multipleTips_card_le_six G hΔ Q h21 r hfull
  have htip : (rootTips G Q r).card ≤ 6 := by
    by_cases hs : (singleTips G Q r).Nonempty
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
      exact rootTips_card_le_six_of_single G hΔ Q hQ hN
        ((G.mem_neighborFinset r a).mp haN) hxT e heQ he
    · exact (card_le_card (rootTips_subset_multiple_of_no_single G Q r hs)).trans hp
  have hfd := fullDoubleTips_card_le_four G hΔ Q hQ hN
  have hroot := rootEdges_card_le_tips_add_fullDoubleTips G Q r hN ht
  by_cases hf : (fullDoubleTips G Q r).card = 4
  · have hs := card_le_card (rootTips_subset_fullDoubleTips_of_four G hΔ Q hQ hN ht hf)
    omega
  by_cases hf3 : (fullDoubleTips G Q r).card = 3
  · obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (fullDoubleTips G Q r).card by omega)
    by_cases heq : ∀ y ∈ fullDoubleTips G Q r, rootType G r y = rootType G r x
    · have hb := rootTips_card_le_five_of_three_equal_full_double_types G hΔ Q hQ hN ht hx hf3 heq
      omega
    · obtain ⟨y, hy⟩ := not_forall.mp heq
      have hyD : y ∈ fullDoubleTips G Q r := by by_contra hn; exact hy (fun h => (hn h).elim)
      have hne : rootType G r y ≠ rootType G r x := fun h => hy (fun _ => h)
      have hdis := (high21_full_double_types_equal_or_disjoint G hΔ Q hQ h21 hN hyD hx).resolve_left hne
      have hb := rootTips_card_le_four_of_disjoint_full_double_types G hΔ Q hQ hN ht hyD hx hdis
      omega
  · omega

theorem high21_clique_card_le_sixteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 16 := by
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    exact high21_clique_card_le_sixteen_of_root_triple G hΔ Q hQ h21 r hR hxr hx
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
    omega
  have hk := high21_small_types_rootEdges_card_le_eight G hΔ Q hQ h21 hR ht
  have hN := high21_root_neighborhood_independent G hΔ Q h21 r (by omega)
  have ho := outer_card_le_four_of_double_types G hΔ Q hQ r hR hN ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  omega

end StrongEdge19
