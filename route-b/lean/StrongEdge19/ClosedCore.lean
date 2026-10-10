module

public import StrongEdge19.QuadCore

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high19_large_quad_residual_closed
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4)
    (hzr : z ≠ r) (hz : (rootType G r z).card = 4) :
    ∀ x ∈ (multipleTips G r).erase z,
      G.neighborFinset x \ G.neighborFinset r ⊆ (multipleTips G r).erase z := by
  let D := (multipleTips G r).erase z
  obtain ⟨hP5, _, hlo, hhi⟩ := high19_large_quad_counts G hΔ Q hQ h19 hq hR hzr hz
  have hzP : z ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
  have hDc : D.card = 4 := by have hc := card_erase_add_one hzP; dsimp [D]; omega
  have hsmall := high19_large_quad_other_types_le_two G hΔ Q hQ h19 hq hR hzr hz
  have htwo : ∀ x ∈ D, (rootType G r x).card = 2 := by
    intro x hx
    have hx' := mem_erase.mp hx
    have hxP := (mem_filter.mp hx'.2).2
    have hb := hsmall x hxP.1 hx'.1
    omega
  have hN := high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) r hR
  by_cases ho : (outerEdges G Q r).card = 4
  · have hOD := high19_large_quad_outer_supported G hΔ Q hQ h19 hq hR hzr hz
    intro x hx
    have hinc := four_outer_edges_saturate_multiple_support G hΔ Q r D
      (erase_subset _ _) (by omega) hOD ho hx
    have hres := residual_neighbors_add_type_card G r x
    have hdx := hΔ x
    have ht := htwo x hx
    have hi := restricted_incidence_card_le G (outerEdges G Q r) D hOD x
    have hsub : G.neighborFinset x ∩ D ⊆ G.neighborFinset x \ G.neighborFinset r := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, fun hn =>
        multipleTips_not_neighbor G hN (mem_erase.mp (mem_inter.mp hy).2).2
          ((G.mem_neighborFinset r y).mp hn)⟩
    have heq : G.neighborFinset x ∩ D = G.neighborFinset x \ G.neighborFinset r :=
      eq_of_subset_of_card_le hsub (by omega)
    rw [← heq]
    exact inter_subset_right
  · obtain ⟨_, hfull⟩ := labels_saturated_of_card_ge_sixteen_add_outer G hΔ Q r (by omega)
    have heq : fullDoubleTips G Q r = D := by
      ext x
      constructor
      · intro hx
        obtain ⟨_, hxr, ht, _⟩ := mem_filter.mp hx
        have hxz : x ≠ z := by intro h; subst x; omega
        exact mem_erase.mpr ⟨hxz, mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩⟩
      · intro hx
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_erase.mp hx).2).2.1,
          htwo x hx, hfull x⟩
    intro x hx
    have h := fullDoubleTips_saturated_of_four G hΔ Q hQ hN
      (by rw [heq]; exact hDc) (by rw [heq]; exact hx)
    simpa only [heq] using h

/-- A large high-nineteen clique is supported on a closed original set of at most ten vertices. -/
theorem high19_large_clique_closed_ten_support
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card) :
    ∃ S : Finset V, S.card ≤ 10 ∧
      (∀ e ∈ Q, ∀ x ∈ e.val, x ∈ S) ∧
      (∀ x ∈ S, G.neighborFinset x ⊆ S) := by
  obtain ⟨r, hR⟩ := large_clique_exists_root_four G hΔ Q hQ (by omega)
  obtain ⟨z, hzr, hz⟩ := high19_large_clique_exists_type_four G hΔ Q hQ h19 hq r hR
  let A := G.neighborFinset r
  let P := multipleTips G r
  let S := insert r (A ∪ P)
  have hP5 := (high19_large_quad_counts G hΔ Q hQ h19 hq hR hzr hz).1
  have htip := high19_large_quad_positive_type_support G hΔ Q hQ h19 hq hR hzr hz
  have houter := high19_large_quad_outer_supported G hΔ Q hQ h19 hq hR hzr hz
  have hclosed := high19_large_quad_residual_closed G hΔ Q hQ h19 hq hR hzr hz
  have hA4 : A.card = 4 := by
    have hc := card_le_card (rootLabels_subset_neighbors G Q r)
    have hd := hΔ r
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    change G.degree r = 4
    omega
  have hzType : rootType G r z = A := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hzNeigh : G.neighborFinset z = A := by
    apply neighbors_eq_of_four_subset G hΔ z A hA4
    intro a ha
    exact (G.mem_neighborFinset z a).mpr ((mem_rootType G r z a).mp (hzType.symm ▸ ha)).2
  refine ⟨S, ?_, ?_, ?_⟩
  · have hi := card_insert_le r (A ∪ P)
    have hu := card_union_le A P
    change P.card = 5 at hP5
    change (insert r (A ∪ P)).card ≤ 10
    omega
  · intro e heQ x hxe
    by_cases hxr : x = r
    · exact mem_insert.mpr (Or.inl hxr)
    by_cases hxA : x ∈ A
    · exact mem_insert_of_mem (mem_union_left _ hxA)
    apply mem_insert_of_mem
    apply mem_union_right
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
    have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
    by_cases hyA : y ∈ A
    · exact htip x hxr (card_pos.mpr ⟨y, (mem_rootType G r x y).mpr
        ⟨(G.mem_neighborFinset r y).mp hyA, hxy⟩⟩)
    have hyr : y ≠ r := fun h => hxA ((G.mem_neighborFinset r x).mpr (h ▸ hxy.symm))
    have heo : e ∈ outerEdges G Q r := by
      apply mem_filter.mpr
      refine ⟨heQ, ?_, ?_⟩
      · rw [hey, Sym2.mem_iff]; tauto
      · rw [hey, Sym2.forall_mem_pair]
        exact ⟨fun h => hxA ((G.mem_neighborFinset r x).mpr h),
          fun h => hyA ((G.mem_neighborFinset r y).mpr h)⟩
    exact (mem_erase.mp (houter e heo x hxe)).2
  · intro x hx y hy
    rcases mem_insert.mp hx with hxr | hx
    · subst x
      exact mem_insert_of_mem (mem_union_left _ hy)
    rcases mem_union.mp hx with hxA | hxP
    · by_cases hyr : y = r
      · exact mem_insert.mpr (Or.inl hyr)
      apply mem_insert_of_mem
      apply mem_union_right
      exact htip y hyr (card_pos.mpr ⟨x, (mem_rootType G r y x).mpr
        ⟨(G.mem_neighborFinset r x).mp hxA, ((G.mem_neighborFinset x y).mp hy).symm⟩⟩)
    · by_cases hxz : x = z
      · subst x
        exact mem_insert_of_mem (mem_union_left _ (hzNeigh ▸ hy))
      by_cases hyA : y ∈ A
      · exact mem_insert_of_mem (mem_union_left _ hyA)
      exact mem_insert_of_mem (mem_union_right _
        (mem_erase.mp (hclosed x (mem_erase.mpr ⟨hxz, hxP⟩) (mem_sdiff.mpr ⟨hy, hyA⟩))).2)

end StrongEdge19
