module

public import StrongEdge19.RootSaturation

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
theorem edges_supported_on_two_card_le_one
    (Q : Finset G.edgeSet) (P : Finset V) (hPc : P.card ≤ 2)
    (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P) : Q.card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huv : u ≠ v := (G.mem_edgeSet.mp (hev ▸ e.property)).ne
  have hp : P = {u, v} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hx
      rcases mem_insert.mp hx with hx | hx
      · rw [hx]
        exact hP e he u (hev ▸ Sym2.mem_mk_left u v)
      · rw [mem_singleton.mp hx]
        exact hP e he v (hev ▸ Sym2.mem_mk_right u v)
    · simpa only [card_pair huv] using hPc
  obtain ⟨x, y, hfv⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = f.val from ⟨f.val, rfl⟩)
  have hx := hP f hf x (hfv ▸ Sym2.mem_mk_left x y)
  have hy := hP f hf y (hfv ▸ Sym2.mem_mk_right x y)
  have hxy : x ≠ y := (G.mem_edgeSet.mp (hfv ▸ f.property)).ne
  simp only [hp, mem_insert, mem_singleton] at hx hy
  apply Subtype.ext
  rw [← hev, ← hfv]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hxy rfl).elim

/-- A leaf in the original restricted graph permits at most three clique edges. -/
theorem restricted_degree_two_clique_at_leaf_card_le_three
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (P : Finset V) (hP : ∀ e ∈ Q, ∀ x ∈ e.val, x ∈ P)
    (hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2)
    {u v : V} (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(u, v))
    (hu1 : (G.neighborFinset u ∩ P).card ≤ 1) : Q.card ≤ 3 := by
  have hu := hP e heQ u (he.symm ▸ Sym2.mem_mk_left u v)
  have hv := hP e heQ v (he.symm ▸ Sym2.mem_mk_right u v)
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have heq : endpointNeighbourCover G u v ∩ P =
      ((G.neighborFinset u ∩ P).erase v) ∪ ((G.neighborFinset v ∩ P).erase u) := by
    ext w
    simp only [endpointNeighbourCover, mem_inter, mem_union, mem_erase]
    tauto
  have hcu := card_erase_add_one (mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hv⟩)
  have hcv := card_erase_add_one (mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr huv.symm, hu⟩)
  have hdv := hd v hv
  have hb := card_union_le ((G.neighborFinset u ∩ P).erase v) ((G.neighborFinset v ∩ P).erase u)
  have hc : (endpointNeighbourCover G u v ∩ P).card ≤ 1 := by rw [heq]; omega
  have hcount := clique_card_le_one_add_restricted_incidence_sum G Q hQ P hP e heQ he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v ∩ P) (fun w hw =>
    (restricted_incidence_card_le G Q P hP w).trans (hd w (mem_inter.mp hw).2))
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem multiple_restricted_degree_add_type_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) {r : V}
    (hN : G.IsIndepSet (G.neighborSet r)) (x : V) :
    (G.neighborFinset x ∩ multipleTips G r).card + (rootType G r x).card ≤ 4 := by
  have hs : G.neighborFinset x ∩ multipleTips G r ⊆
      G.neighborFinset x \ G.neighborFinset r := by
    intro y hy
    exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, fun h =>
      multipleTips_not_neighbor G hN (mem_inter.mp hy).2 ((G.mem_neighborFinset r y).mp h)⟩
  have hc := card_le_card hs
  have hi := residual_neighbors_add_type_card G r x
  have hd := hΔ x
  omega

variable [DecidableRel (conflictGraph G).Adj]

/-- Two triple types force fewer than four outer edges at threshold nineteen. -/
theorem high19_two_triples_outer_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hR : (rootLabels G Q r).card = 4)
    {x y : V} (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card) :
    (outerEdges G Q r).card ≤ 3 := by
  by_contra hn
  let P := multipleTips G r
  let O := outerEdges G Q r
  let D := (P.erase x).erase y
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hxP : x ∈ P := mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩
  have hyP : y ∈ P.erase x := mem_erase.mpr ⟨hxy.symm,
    mem_filter.mpr ⟨mem_univ _, hyr, by omega⟩⟩
  have hcx := card_erase_add_one hxP
  have hcy := card_erase_add_one hyP
  have hlow := multipleTips_sum_ge_twice_card_add_two_of_two_triples G hxr hyr hxy hx hy
  have hsum := multipleTips_type_sum_le_twelve G hΔ r
  have hPc : P.card ≤ 5 := by change 2 * P.card + 2 ≤ _ at hlow; omega
  have ht : ∀ z, z ≠ r → z ≠ x → z ≠ y → (rootType G r z).card ≤ 2 := by
    intro z hzr hzx hzy
    by_contra h
    exact high19_no_three_triple_types G hΔ Q h19 hN hfull hxr hyr hzr
      hxy hzx.symm hzy.symm hx hy (by omega)
  let R := O.filter (fun e => x ∉ e.val ∧ y ∉ e.val)
  have hRD : ∀ e ∈ R, ∀ z ∈ e.val, z ∈ D := by
    intro e he
    obtain ⟨heo, hxe, hye⟩ := mem_filter.mp he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have ends := outerEdges_endpoints G Q r e hev.symm heo
    have hux : u ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_left u v)
    have hvx : v ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_right u v)
    have huy : u ≠ y := fun h => hye (hev ▸ h ▸ Sym2.mem_mk_left u v)
    have hvy : v ≠ y := fun h => hye (hev ▸ h ▸ Sym2.mem_mk_right u v)
    have hu := ht u ends.2.1 hux huy
    have hv := ht v ends.2.2.1 hvx hvy
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    rw [← hev, Sym2.forall_mem_pair]
    exact ⟨mem_erase.mpr ⟨huy, mem_erase.mpr ⟨hux, mem_filter.mpr ⟨mem_univ _, ends.2.1, by omega⟩⟩⟩,
      mem_erase.mpr ⟨hvy, mem_erase.mpr ⟨hvx, mem_filter.mpr ⟨mem_univ _, ends.2.2.1, by omega⟩⟩⟩⟩
  have hix := outer_incidence_add_type_card_le_degree G Q r x
  have hiy := outer_incidence_add_type_card_le_degree G Q r y
  have hdx := hΔ x
  have hdy := hΔ y
  have hOsub : O ⊆ edgeIncidences G O x ∪ edgeIncidences G O y ∪ R := by
    intro e he
    by_cases hxe : x ∈ e.val
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨he, hxe⟩))
    by_cases hye : y ∈ e.val
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨he, hye⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨he, hxe, hye⟩)
  have hOc := (card_le_card hOsub).trans (card_union_le _ _)
  have hOc' := card_union_le (edgeIncidences G O x) (edgeIncidences G O y)
  have hP5 : P.card = 5 := by
    by_contra hp
    have hD2 : D.card ≤ 2 := by dsimp [D]; omega
    have hR1 := edges_supported_on_two_card_le_one G R D hD2 hRD
    change ¬ O.card ≤ 3 at hn
    change (edgeIncidences G O x).card + _ ≤ _ at hix
    change (edgeIncidences G O y).card + _ ≤ _ at hiy
    omega
  have hOP : ∀ e ∈ O, ∀ z ∈ e.val, z ∈ P := by
    intro e heo
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have ends := outerEdges_endpoints G Q r e hev.symm heo
    have hcov := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    have hu0 : 0 < (edgeIncidences G O u).card := card_pos.mpr
      ⟨e, mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_left u v⟩⟩
    have hv0 : 0 < (edgeIncidences G O v).card := card_pos.mpr
      ⟨e, mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_right u v⟩⟩
    have hui := outer_incidence_add_type_card_le_degree G Q r u
    have hvi := outer_incidence_add_type_card_le_degree G Q r v
    have hdu := hΔ u
    have hdv := hΔ v
    have hnu := no_single_type_of_five_multiple_two_triples G hΔ hxr hyr hxy hx hy hP5 ends.2.1
    have hnv := no_single_type_of_five_multiple_two_triples G hΔ hxr hyr hxy hx hy hP5 ends.2.2.1
    change (edgeIncidences G O u).card + _ ≤ _ at hui
    change (edgeIncidences G O v).card + _ ≤ _ at hvi
    rw [← hev, Sym2.forall_mem_pair]
    exact ⟨mem_filter.mpr ⟨mem_univ _, ends.2.1, by omega⟩,
      mem_filter.mpr ⟨mem_univ _, ends.2.2.1, by omega⟩⟩
  have hdeg : ∀ z ∈ P, (G.neighborFinset z ∩ P).card ≤ 2 := by
    intro z hz
    have hm := multiple_restricted_degree_add_type_le_four G hΔ hN z
    have hz2 := (mem_filter.mp hz).2.2
    change (G.neighborFinset z ∩ P).card + _ ≤ _ at hm
    omega
  have hOQ : (conflictGraph G).IsClique (O : Set G.edgeSet) :=
    fun e he f hf hef => hQ (mem_filter.mp he).1 (mem_filter.mp hf).1 hef
  have hno : ∀ z, 3 ≤ (rootType G r z).card → ∀ e ∈ O, z ∉ e.val := by
    intro z hz3 e he hze
    obtain ⟨w, hew⟩ := Sym2.mem_iff_exists.mp hze
    have hm := multiple_restricted_degree_add_type_le_four G hΔ hN z
    have hz1 : (G.neighborFinset z ∩ P).card ≤ 1 := by
      change (G.neighborFinset z ∩ P).card + _ ≤ _ at hm
      omega
    have hb := restricted_degree_two_clique_at_leaf_card_le_three G O hOQ P hOP hdeg e he hew hz1
    exact hn hb
  have hOD : ∀ e ∈ O, ∀ z ∈ e.val, z ∈ D := by
    intro e he z hze
    exact mem_erase.mpr ⟨fun h => hno y hy e he (h ▸ hze),
      mem_erase.mpr ⟨fun h => hno x hx e he (h ▸ hze), hOP e he z hze⟩⟩
  have hinc := outer_incidence_sum_eq_twice G Q r D hOD
  have hb := sum_le_sum (s := D) (fun z hz =>
    (restricted_incidence_card_le G O P hOP z).trans
      (hdeg z (mem_erase.mp (mem_erase.mp hz).2).2))
  simp only [sum_const, smul_eq_mul] at hb
  change ∑ z ∈ D, (edgeIncidences G O z).card = 2 * O.card at hinc
  change ¬ O.card ≤ 3 at hn
  dsimp [D] at hb hinc
  omega

end StrongEdge19
