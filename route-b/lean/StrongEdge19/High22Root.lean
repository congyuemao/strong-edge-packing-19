module

public import StrongEdge19.SmallTypes
public import StrongEdge19.TypeCover

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- Four selected outer edges on at most four multiple tips violate full threshold twenty-one. -/
theorem four_outer_edges_impossible_at_high21
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r : V} (hR : (rootLabels G Q r).card = 4)
    (P : Finset V) (hP : P ⊆ multipleTips G r) (hPc : P.card ≤ 4)
    (hOP : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P)
    (ho : (outerEdges G Q r).card = 4) : False := by
  obtain ⟨e, heo⟩ := card_pos.mp (show 0 < (outerEdges G Q r).card by omega)
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have he : e.val = s(u, v) := hev.symm
  have hu := hOP e heo u (hev ▸ Sym2.mem_mk_left u v)
  have hv := hOP e heo v (hev ▸ Sym2.mem_mk_right u v)
  have hiu := four_outer_edges_saturate_multiple_support G hΔ Q r P hP hPc hOP ho hu
  have hiv := four_outer_edges_saturate_multiple_support G hΔ Q r P hP hPc hOP ho hv
  obtain ⟨x, hxv, hux, f, hfo, hfx⟩ := exists_other_outer_neighbor G Q e he heo (by omega)
  obtain ⟨y, hyu, hvy, g, hgo, hgy⟩ := exists_other_outer_neighbor G Q e (he.trans Sym2.eq_swap) heo (by omega)
  have hxP := hP (hOP f hfo x (hfx.symm ▸ Sym2.mem_mk_right u x))
  have hyP := hP (hOP g hgo y (hgy.symm ▸ Sym2.mem_mk_right v y))
  have hx2 := (mem_filter.mp hxP).2.2
  have hy2 := (mem_filter.mp hyP).2.2
  have he21 := h21 e (mem_filter.mp heo).1
  have hxy : x ≠ y := fun h => high21_no_triangle_on_edge G hΔ e he he21 hux (h.symm ▸ hvy)
  have hxN : x ∉ G.neighborFinset r := fun h =>
    (outerEdges_endpoints G Q r f hfx hfo).2.2.2.2 ((G.mem_neighborFinset r x).mp h)
  have hyN : y ∉ G.neighborFinset r := fun h =>
    (outerEdges_endpoints G Q r g hgy hgo).2.2.2.2 ((G.mem_neighborFinset r y).mp h)
  have hxC : x ∈ endpointNeighbourCover G u v :=
    mem_union_left _ (mem_erase.mpr ⟨hxv, (G.mem_neighborFinset u x).mpr hux⟩)
  have hyC : y ∈ endpointNeighbourCover G u v :=
    mem_union_right _ (mem_erase.mpr ⟨hyu, (G.mem_neighborFinset v y).mpr hvy⟩)
  have hb := two_type_stars_inside G hxy hxN hyN (endpointNeighbourCover G u v) hxC hyC
    (outer_root_neighborhood_subset_cover G hΔ Q hQ hR e he heo)
  have hc := high21_cover_inside_card_le_three G hΔ e he he21
  omega

theorem high22_clique_card_le_fifteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 15 := by
  have h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e := fun e he => by have h := h22 e he; omega
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high22_root_neighborhood_independent G hΔ Q h22 r (by omega)
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    have hx3 : (rootType G r x).card = 3 := by
      have hb := high22_root_type_card_le_three G hΔ Q h22 r (by omega) hxr
      omega
    have ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
      intro y hyr hyx
      by_contra hn
      exact hyx (high22_multipleTips_eq_of_triple G hΔ Q h22 r hfull hxr hx
        (mem_filter.mpr ⟨mem_univ _, hyr, by omega⟩))
    have hk := root_card_le_ten_of_unique_triple G hΔ Q hQ hN hR hx3 ht
    have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x := by
      intro e heo
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      have ends := outerEdges_endpoints G Q r e hev.symm heo
      have hb := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
        (card_union_le _ _)
      apply mem_filter.mpr
      refine ⟨heo, ?_⟩
      by_cases hu : 2 ≤ (rootType G r u).card
      · have heq := high22_multipleTips_eq_of_triple G hΔ Q h22 r hfull hxr hx
          (mem_filter.mpr ⟨mem_univ _, ends.2.1, hu⟩)
        exact heq ▸ (hev ▸ Sym2.mem_mk_left u v)
      · have heq := high22_multipleTips_eq_of_triple G hΔ Q h22 r hfull hxr hx
          (mem_filter.mpr ⟨mem_univ _, ends.2.2.1, by omega⟩)
        exact heq ▸ (hev ▸ Sym2.mem_mk_right u v)
    have ho := card_le_card hs
    have hi := outer_incidence_add_type_card_le_degree G Q r x
    have hd := hΔ x
    omega
  · have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
      intro x hxr
      have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
      omega
    have hk := high21_small_types_rootEdges_card_le_eight G hΔ Q hQ h21 hR ht
    have ho := outer_card_le_four_of_double_types G hΔ Q hQ r hR hN ht
    have hp := high22_multipleTips_card_le_four G hΔ Q h22 r hfull
    have hn : (outerEdges G Q r).card ≠ 4 := fun h =>
      four_outer_edges_impossible_at_high21 G hΔ Q hQ h21 hR (multipleTips G r) (Subset.refl _)
        hp (outer_endpoints_multiple_of_root_four G Q hQ r hR ht) h
    omega

end StrongEdge19
