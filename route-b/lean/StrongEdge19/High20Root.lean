module

public import StrongEdge19.High20Triple
public import StrongEdge19.SmallTypes

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The upstream quadruple argument already bounds the outer part by one. -/
theorem high20_outer_card_le_one_of_root_type_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 4 ≤ (rootType G r x).card) :
    (outerEdges G Q r).card ≤ 1 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  let O := (outerEdges G Q r).filter (fun e => x ∉ e.val)
  have hO : O.card ≤ 1 := by
    apply card_le_one.mpr
    intro e he f hf
    obtain ⟨heo, hxe⟩ := mem_filter.mp he
    obtain ⟨hfo, hxf⟩ := mem_filter.mp hf
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    obtain ⟨p, q, hfq⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = f.val from ⟨f.val, rfl⟩)
    have hs := high20_multipleTips_subset_four_outer_endpoints G hΔ Q hQ h20 hN hR hxr hx
      e heo hev.symm hxe
    have hends := outerEdges_endpoints G Q r f hfq.symm hfo
    have hpx : p ≠ x := fun h => hxf (hfq ▸ h ▸ Sym2.mem_mk_left p q)
    have hqx : q ≠ x := fun h => hxf (hfq ▸ h ▸ Sym2.mem_mk_right p q)
    have hp := high20_other_type_le_two_of_four G hΔ Q h20 hN hfull hxr hx hends.2.1 hpx
    have hq := high20_other_type_le_two_of_four G hΔ Q h20 hN hfull hxr hx hends.2.2.1 hqx
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r f hfq.symm hfo)).trans
      (card_union_le _ _)
    have hpm := hs (mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩)
    have hqm := hs (mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩)
    simp only [mem_insert, mem_singleton, hpx, hqx, false_or] at hpm hqm
    have hpq : p ≠ q := (G.mem_edgeSet.mp (hfq ▸ f.property)).ne
    apply Subtype.ext
    rw [← hev, ← hfq]
    rcases hpm with rfl | rfl <;> rcases hqm with rfl | rfl
    · exact (hpq rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hpq rfl).elim
  have hpart : (outerEdges G Q r).card = (edgeIncidences G (outerEdges G Q r) x).card + O.card := by
    exact (card_filter_add_card_filter_not (s := outerEdges G Q r) (p := fun e => x ∈ e.val)).symm
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hd := hΔ x
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem small_types_clique_card_le_seventeen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) : Q.card ≤ 17 := by
  have hp := multipleTips_card_le_six G hΔ r
  have htip : (rootTips G Q r).card ≤ 6 := by
    by_cases hsingle : (singleTips G Q r).Nonempty
    · obtain ⟨x, hx⟩ := hsingle
      obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
      exact rootTips_card_le_six_of_single G hΔ Q hQ hN ((G.mem_neighborFinset r a).mp haN)
        hxT e heQ he
    · exact (card_le_card (rootTips_subset_multiple_of_no_single G Q r hsingle)).trans hp
  have hfd := fullDoubleTips_card_le_four G hΔ Q hQ hN
  have hroot := rootEdges_card_le_tips_add_fullDoubleTips G Q r hN ht
  have ho := outer_card_le_four_of_double_types G hΔ Q hQ r hR hN ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card G Q r, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hf : (fullDoubleTips G Q r).card = 4
  · have hs := card_le_card (rootTips_subset_fullDoubleTips_of_four G hΔ Q hQ hN ht hf)
    omega
  · omega

/-- All original-edge strong cliques above full threshold twenty have at most seventeen edges. -/
theorem high20_clique_card_le_seventeen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) : Q.card ≤ 17 := by
  by_contra hn
  obtain ⟨r, hR⟩ := large_clique_exists_root_four G hΔ Q hQ (by omega)
  have h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e := fun e he => by have h := h20 e he; omega
  have hN := high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) r hR
  by_cases hquad : ∃ x, x ≠ r ∧ 4 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := hquad
    have ho := high20_outer_card_le_one_of_root_type_four G hΔ Q hQ h20 hN hR hxr hx
    have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
    have hsum := sum_le_sum (s := G.neighborFinset r)
      (fun y _ => (edgeIncidences_card_le_degree G Q y).trans (hΔ y))
    have hdr := hΔ r
    have hc := selected_edges_card_le_meeting_add_outer G Q r
    simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
    omega
  have ht3 : ∀ x, x ≠ r → (rootType G r x).card ≤ 3 := by
    intro x hxr
    have hn : ¬ 4 ≤ (rootType G r x).card := fun h => hquad ⟨x, hxr, h⟩
    omega
  by_cases htriple : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htriple
    by_cases htwo : ∃ y, y ≠ r ∧ y ≠ x ∧ 3 ≤ (rootType G r y).card
    · obtain ⟨y, hyr, hyx, hy⟩ := htwo
      have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x ∪
          edgeIncidences G (outerEdges G Q r) y := by
        intro e he
        rcases high20_outer_meets_two_triples G hΔ Q hQ h20 hN hR hxr hyr hyx.symm hx hy e he with h | h
        · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨he, h⟩)
      have ho := (card_le_card hs).trans (card_union_le _ _)
      have hix := outer_incidence_add_type_card_le_degree G Q r x
      have hiy := outer_incidence_add_type_card_le_degree G Q r y
      have hdx := hΔ x
      have hdy := hΔ y
      obtain ⟨hdA, hfull⟩ := labels_saturated_of_card_ge_sixteen_add_outer G hΔ Q r (by omega)
      have hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a) := by
        intro a ha
        apply high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) a
        rw [rootLabels_card, hdA a ha]
      have hNr : (G.neighborFinset r).card = 4 := by
        have hc := card_le_card (rootLabels_subset_neighbors G Q r)
        have hd := hΔ r
        simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc ⊢
        omega
      exact no_triple_of_saturated_independent_labels G hΔ Q hQ hN hA hdA hfull ht3 hNr hxr hx
    · have ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
        intro y hyr hyx
        have hn : ¬ 3 ≤ (rootType G r y).card := fun h => htwo ⟨y, hyr, hyx, h⟩
        omega
      have hx3 : (rootType G r x).card = 3 := by have hb := ht3 x hxr; omega
      have hk := root_card_le_ten_of_unique_triple G hΔ Q hQ hN hR hx3 ht
      have ho := high20_unique_triple_outer_card_le_three G hΔ Q hQ h20 hN hR hxr hx3 ht
      have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card G Q r, hR]
      have hc := clique_card_le_star_root_outer G Q r
      omega
  · apply hn
    apply small_types_clique_card_le_seventeen G hΔ Q hQ r hR hN
    intro x hxr
    have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htriple ⟨x, hxr, h⟩
    omega

end StrongEdge19
