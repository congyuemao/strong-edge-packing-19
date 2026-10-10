module

public import StrongEdge19.OuterSaturation

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- A unique triple permits at most three outer edges at full threshold twenty. -/
theorem high20_unique_triple_outer_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) :
    (outerEdges G Q r).card ≤ 3 := by
  by_contra hn
  let O := outerEdges G Q r
  let R := O.filter (fun e => x ∉ e.val)
  let P := (multipleTips G r).erase x
  have ho4 : O.card = 4 := by
    have hb := outer_card_le_four_of_unique_triple G hΔ Q hQ hN hR hxr hx ht
    change ¬ O.card ≤ 3 at hn
    change O.card ≤ 4 at hb
    omega
  have hPsub : P ⊆ multipleTips G r := erase_subset _ _
  have hPc : P.card ≤ 4 := multipleTips_erase_card_le_four_of_triple G hΔ hxr (by omega)
  have hRsub : R ⊆ O := filter_subset _ _
  have hReq : outerEdges G R r = R := outerEdges_eq_self_of_subset G Q R r hRsub
  have hRP : ∀ e ∈ R, ∀ y ∈ e.val, y ∈ P := by
    intro e he y hye
    obtain ⟨heo, hxe⟩ := mem_filter.mp he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have ends := outerEdges_endpoints G Q r e hev.symm heo
    have hux : u ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_left u v)
    have hvx : v ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_right u v)
    have hu := ht u ends.2.1 hux
    have hv := ht v ends.2.2.1 hvx
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    rw [← hev, Sym2.mem_iff] at hye
    rcases hye with rfl | rfl
    · exact mem_erase.mpr ⟨hux, mem_filter.mpr ⟨mem_univ _, ends.2.1, by omega⟩⟩
    · exact mem_erase.mpr ⟨hvx, mem_filter.mpr ⟨mem_univ _, ends.2.2.1, by omega⟩⟩
  have hRP' : ∀ e ∈ outerEdges G R r, ∀ y ∈ e.val, y ∈ P := by simpa only [hReq] using hRP
  have hix := outer_incidence_add_type_card_le_degree G Q r x
  have hdx := hΔ x
  change (edgeIncidences G O x).card + _ ≤ _ at hix
  have hix1 : (edgeIncidences G O x).card ≤ 1 := by omega
  by_cases hi0 : (edgeIncidences G O x).card = 0
  · have hOP : ∀ e ∈ O, ∀ y ∈ e.val, y ∈ P := by
      intro e he y hye
      have hxe : x ∉ e.val := fun h =>
        notMem_empty e ((card_eq_zero.mp hi0) ▸ mem_filter.mpr ⟨he, h⟩)
      exact hRP e (mem_filter.mpr ⟨he, hxe⟩) y hye
    exact four_outer_edges_impossible_at_high20 G hΔ Q hQ h20 hR P hPsub hPc hOP ho4
  have hpart := card_filter_add_card_filter_not (s := O) (p := fun e => x ∈ e.val)
  change (edgeIncidences G O x).card + R.card = O.card at hpart
  have hR3 : R.card = 3 := by omega
  obtain ⟨u, hu, v, hv, f, hf, hfv, hsu, hsv⟩ := three_outer_edges_have_saturated_pair
    G hΔ R r P hPsub hPc hRP' (by rw [hReq]; exact hR3)
  have hsatu : 4 ≤ (edgeIncidences G (outerEdges G R r) u).card + (rootType G r u).card := by
    have hu2 := (mem_filter.mp (hPsub hu)).2.2
    omega
  have hsatv : 4 ≤ (edgeIncidences G (outerEdges G R r) v).card + (rootType G r v).card := by
    have hv2 := (mem_filter.mp (hPsub hv)).2.2
    omega
  have hfR : f ∈ R := hReq ▸ hf
  obtain ⟨e, heI⟩ := card_pos.mp (show 0 < (edgeIncidences G O x).card by omega)
  obtain ⟨heo, hxe⟩ := mem_filter.mp heI
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have ends := outerEdges_endpoints G Q r e hey heo
  have hxp : x ∉ P := notMem_erase _ _
  have hyP : y ∈ P := by
    by_contra hyp
    have hfe : f ≠ e := fun h => (mem_filter.mp hfR).2 (h.symm ▸ hxe)
    obtain ⟨z, hzC, hze⟩ := strongConflict_meets_cover G hfv
      (hQ (mem_filter.mp (hRsub hfR)).1 ends.1 hfe)
    rw [hey, Sym2.mem_iff] at hze
    have hn : ¬ G.Adj r z ∧ z ∉ P := by
      rcases hze with rfl | rfl
      · exact ⟨ends.2.2.2.1, hxp⟩
      · exact ⟨ends.2.2.2.2, hyp⟩
    rcases mem_union.mp hzC with hz | hz
    · exact (outer_saturated_neighbors G hΔ R r P hRP' hsatu
        ((G.mem_neighborFinset u z).mp (mem_erase.mp hz).2)).elim hn.1 hn.2
    · exact (outer_saturated_neighbors G hΔ R r P hRP' hsatv
        ((G.mem_neighborFinset v z).mp (mem_erase.mp hz).2)).elim hn.1 hn.2
  have hxP : x ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩
  have hOP : ∀ g ∈ O, ∀ z ∈ g.val, z ∈ multipleTips G r := by
    intro g hg z hzg
    by_cases hxg : x ∈ g.val
    · have hge := card_le_one.mp hix1 g (mem_filter.mpr ⟨hg, hxg⟩) e heI
      rw [hge, hey, Sym2.mem_iff] at hzg
      rcases hzg with rfl | rfl
      · exact hxP
      · exact hPsub hyP
    · exact hPsub (hRP g (mem_filter.mpr ⟨hg, hxg⟩) z hzg)
  have hd : ∀ z ∈ multipleTips G r, (G.neighborFinset z ∩ multipleTips G r).card ≤ 2 := by
    intro z hz
    have hb := multiple_restricted_degree_add_type_le_four G hΔ hN z
    have hz2 := (mem_filter.mp hz).2.2
    omega
  have hx1 : (G.neighborFinset x ∩ multipleTips G r).card ≤ 1 := by
    have hb := multiple_restricted_degree_add_type_le_four G hΔ hN x
    omega
  have hOQ : (conflictGraph G).IsClique (O : Set G.edgeSet) :=
    fun a ha b hb hab => hQ (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab
  exact hn (restricted_degree_two_clique_at_leaf_card_le_three G O hOQ (multipleTips G r)
    hOP hd e heo hey hx1)

end StrongEdge19
