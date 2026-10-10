module

public import StrongEdge19.RootLoad

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Distinct external tips contribute distinct original type edges inside a cover. -/
theorem two_type_stars_inside
    {r x y : V} (hxy : x ≠ y)
    (hxn : x ∉ G.neighborFinset r) (hyn : y ∉ G.neighborFinset r)
    (S : Finset V) (hxS : x ∈ S) (hyS : y ∈ S)
    (hA : G.neighborFinset r ⊆ S) :
    (rootType G r x).card + (rootType G r y).card ≤ (edgesInside G univ S).card := by
  let P := (({x, y} : Finset V) ×ˢ G.neighborFinset r).filter (fun p => G.Adj p.1 p.2)
  have hPc : P.card = (rootType G r x).card + (rootType G r y).card := by
    simp only [P, card_eq_sum_ones, sum_filter, sum_product, sum_pair hxy, rootType]
  rw [← hPc]
  apply card_le_via_relation P (edgesInside G univ S) (fun p e => e.val = s(p.1, p.2))
  · intro p hp
    obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    have hpS : p.1 ∈ S := by
      rcases mem_insert.mp hp1 with h | h
      · exact h.symm ▸ hxS
      · exact (mem_singleton.mp h).symm ▸ hyS
    exact ⟨⟨s(p.1, p.2), hpAdj⟩,
      mem_filter.mpr ⟨mem_univ _, Sym2.forall_mem_pair.mpr ⟨hpS, hA hp2⟩⟩, rfl⟩
  · intro p hp q hq e hpe hqe
    have hp1 := (mem_product.mp (mem_filter.mp hp).1).1
    have hq2 := (mem_product.mp (mem_filter.mp hq).1).2
    rcases Sym2.eq_iff.mp (hpe.symm.trans hqe) with h | h
    · exact Prod.ext h.1 h.2
    · have hpN : p.1 ∈ G.neighborFinset r := h.1.symm ▸ hq2
      rcases mem_insert.mp hp1 with hp1 | hp1
      · exact (hxn (hp1 ▸ hpN)).elim
      · exact (hyn ((mem_singleton.mp hp1) ▸ hpN)).elim

/-- An external original edge adds one more edge beyond two disjoint type stars. -/
theorem two_type_stars_inside_add_external_edge
    {r x y : V} (hxy : x ≠ y)
    (hxn : x ∉ G.neighborFinset r) (hyn : y ∉ G.neighborFinset r)
    (S : Finset V) (hxS : x ∈ S) (hyS : y ∈ S)
    (hA : G.neighborFinset r ⊆ S)
    (f : G.edgeSet) (hfS : f ∈ edgesInside G univ S)
    (hfN : ∀ a ∈ f.val, a ∉ G.neighborFinset r) :
    (rootType G r x).card + (rootType G r y).card + 1 ≤ (edgesInside G univ S).card := by
  let P := (({x, y} : Finset V) ×ˢ G.neighborFinset r).filter (fun p => G.Adj p.1 p.2)
  have hPc : P.card = (rootType G r x).card + (rootType G r y).card := by
    simp only [P, card_eq_sum_ones, sum_filter, sum_product, sum_pair hxy, rootType]
  have hb : P.card ≤ ((edgesInside G univ S).erase f).card := by
    apply card_le_via_relation P ((edgesInside G univ S).erase f) (fun p e => e.val = s(p.1, p.2))
    · intro p hp
      obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := mem_product.mp hp
      have hpS : p.1 ∈ S := by
        rcases mem_insert.mp hp1 with h | h
        · exact h.symm ▸ hxS
        · exact (mem_singleton.mp h).symm ▸ hyS
      let e : G.edgeSet := ⟨s(p.1, p.2), hpAdj⟩
      have hef : e ≠ f := fun h => hfN p.2 (h ▸ Sym2.mem_mk_right p.1 p.2) hp2
      exact ⟨e, mem_erase.mpr ⟨hef,
        mem_filter.mpr ⟨mem_univ _, Sym2.forall_mem_pair.mpr ⟨hpS, hA hp2⟩⟩⟩, rfl⟩
    · intro p hp q hq e hpe hqe
      have hp1 := (mem_product.mp (mem_filter.mp hp).1).1
      have hq2 := (mem_product.mp (mem_filter.mp hq).1).2
      rcases Sym2.eq_iff.mp (hpe.symm.trans hqe) with h | h
      · exact Prod.ext h.1 h.2
      · have hpN : p.1 ∈ G.neighborFinset r := h.1.symm ▸ hq2
        rcases mem_insert.mp hp1 with hp1 | hp1
        · exact (hxn (hp1 ▸ hpN)).elim
        · exact (hyn ((mem_singleton.mp hp1) ▸ hpN)).elim
  have hc := card_erase_add_one hfS
  omega

theorem outer_root_neighborhood_subset_cover
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r u v : V} (hR : (rootLabels G Q r).card = 4)
    (e : G.edgeSet) (he : e.val = s(u, v)) (heo : e ∈ outerEdges G Q r) :
    G.neighborFinset r ⊆ endpointNeighbourCover G u v := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have ends := outerEdges_endpoints G Q r e he heo
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e he heo
  intro a ha
  have hau : a ≠ u := fun h => ends.2.2.2.1 ((G.mem_neighborFinset r u).mp (h ▸ ha))
  have hav : a ≠ v := fun h => ends.2.2.2.2 ((G.mem_neighborFinset r v).mp (h ▸ ha))
  rcases mem_union.mp (hcov (hfull.symm ▸ ha)) with h | h
  · exact mem_union_left _ (mem_erase.mpr ⟨hav, (G.mem_neighborFinset u a).mpr ((mem_rootType G r u a).mp h).2⟩)
  · exact mem_union_right _ (mem_erase.mpr ⟨hau, (G.mem_neighborFinset v a).mpr ((mem_rootType G r v a).mp h).2⟩)

theorem exists_other_outer_neighbor
    (Q : Finset G.edgeSet) {r u v : V}
    (e : G.edgeSet) (he : e.val = s(u, v)) (heo : e ∈ outerEdges G Q r)
    (hinc : 2 ≤ (edgeIncidences G (outerEdges G Q r) u).card) :
    ∃ x, x ≠ v ∧ G.Adj u x ∧ ∃ f ∈ outerEdges G Q r, f.val = s(u, x) := by
  have heI : e ∈ edgeIncidences G (outerEdges G Q r) u :=
    mem_filter.mpr ⟨heo, he.symm ▸ Sym2.mem_mk_left u v⟩
  have hc := card_erase_add_one heI
  obtain ⟨f, hf⟩ := card_pos.mp (show 0 < ((edgeIncidences G (outerEdges G Q r) u).erase e).card by omega)
  obtain ⟨hfe, hfI⟩ := mem_erase.mp hf
  obtain ⟨hfo, huf⟩ := mem_filter.mp hfI
  obtain ⟨x, hfx⟩ := Sym2.mem_iff_exists.mp huf
  refine ⟨x, ?_, G.mem_edgeSet.mp (hfx ▸ f.property), f, hfo, hfx⟩
  intro hxv
  exact hfe (Subtype.ext (hfx.trans (hxv ▸ he.symm)))

end StrongEdge19
