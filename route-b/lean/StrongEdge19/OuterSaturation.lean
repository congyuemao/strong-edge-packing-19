module

public import StrongEdge19.OuterSupport
public import StrongEdge19.TypeCover

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Three outer edges on at most four multiple tips contain an edge with two saturated endpoints. -/
theorem three_outer_edges_have_saturated_pair
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    (P : Finset V) (hP : P ⊆ multipleTips G r) (hPc : P.card ≤ 4)
    (hOP : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P)
    (ho : (outerEdges G Q r).card = 3) :
    ∃ u ∈ P, ∃ v ∈ P, ∃ e ∈ outerEdges G Q r,
      e.val = s(u, v) ∧
      (edgeIncidences G (outerEdges G Q r) u).card = 2 ∧
      (edgeIncidences G (outerEdges G Q r) v).card = 2 := by
  let O := outerEdges G Q r
  let d := fun x => (edgeIncidences G O x).card
  have hs := outer_incidence_sum_eq_twice G Q r P hOP
  change ∑ x ∈ P, d x = 2 * O.card at hs
  have hd : ∀ x ∈ P, d x ≤ 2 := by
    intro x hx
    have ht := (mem_filter.mp (hP hx)).2.2
    have hi := outer_incidence_add_type_card_le_degree G Q r x
    have hb := hΔ x
    change d x + _ ≤ _ at hi
    omega
  have hex : ∃ u ∈ P, d u = 2 := by
    by_contra hn
    have hb := sum_le_sum (s := P) (fun x hx => show d x ≤ 1 by
      have hu := hd x hx
      have he : d x ≠ 2 := fun he => hn ⟨x, hx, he⟩
      omega)
    simp only [sum_const, smul_eq_mul] at hb
    change O.card = 3 at ho
    omega
  obtain ⟨u, hu, hdu⟩ := hex
  have hex' : ∃ v ∈ P.erase u, d v = 2 := by
    by_contra hn
    have hb := sum_le_sum (s := P.erase u) (fun x hx => show d x ≤ 1 by
      have hu := hd x (mem_erase.mp hx).2
      have he : d x ≠ 2 := fun he => hn ⟨x, hx, he⟩
      omega)
    have he := sum_erase_add P d hu
    have hc := card_erase_add_one hu
    simp only [sum_const, smul_eq_mul] at hb
    change O.card = 3 at ho
    omega
  obtain ⟨v, hv, hdv⟩ := hex'
  have hci := card_union_add_card_inter (edgeIncidences G O u) (edgeIncidences G O v)
  have hcu := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _) :
    edgeIncidences G O u ∪ edgeIncidences G O v ⊆ O)
  have hi : 0 < (edgeIncidences G O u ∩ edgeIncidences G O v).card := by
    change (edgeIncidences G O u).card = 2 at hdu
    change (edgeIncidences G O v).card = 2 at hdv
    change O.card = 3 at ho
    omega
  obtain ⟨e, he⟩ := card_pos.mp hi
  obtain ⟨heu, hev⟩ := mem_inter.mp he
  exact ⟨u, hu, v, (mem_erase.mp hv).2, e, (mem_filter.mp heu).1,
    (Sym2.mem_and_mem_iff (mem_erase.mp hv).1.symm).mp
      ⟨(mem_filter.mp heu).2, (mem_filter.mp hev).2⟩, hdu, hdv⟩

variable [DecidableRel (conflictGraph G).Adj]

/-- A saturated four-edge outer configuration has five original edges inside one cover. -/
theorem four_outer_edges_impossible_at_high20
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r : V} (hR : (rootLabels G Q r).card = 4)
    (P : Finset V) (hP : P ⊆ multipleTips G r) (hPc : P.card ≤ 4)
    (hOP : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P)
    (ho : (outerEdges G Q r).card = 4) : False := by
  let O := outerEdges G Q r
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hsat : ∀ x ∈ P, (edgeIncidences G O x).card = 2 :=
    fun x hx => four_outer_edges_saturate_multiple_support G hΔ Q r P hP hPc hOP ho hx
  have ht2 : ∀ x ∈ P, (rootType G r x).card = 2 := by
    intro x hx
    have hi := outer_incidence_add_type_card_le_degree G Q r x
    have hs := hsat x hx
    have hb := hΔ x
    have hl := (mem_filter.mp (hP hx)).2.2
    change (edgeIncidences G O x).card + _ ≤ _ at hi
    omega
  have disjoint_types {u v : V} (e : G.edgeSet) (he : e.val = s(u, v)) (heo : e ∈ O) :
      Disjoint (rootType G r u) (rootType G r v) := by
    have hu := ht2 u (hOP e heo u (he.symm ▸ Sym2.mem_mk_left u v))
    have hv := ht2 v (hOP e heo v (he.symm ▸ Sym2.mem_mk_right u v))
    have hc := card_le_card (outer_edge_types_cover_root_labels G Q hQ r e he heo)
    have hi := card_union_add_card_inter (rootType G r u) (rootType G r v)
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    omega
  obtain ⟨e, heo⟩ := card_pos.mp (show 0 < O.card by change O.card = 4 at ho; omega)
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have he : e.val = s(u, v) := hev.symm
  have hu := hOP e heo u (hev ▸ Sym2.mem_mk_left u v)
  have hv := hOP e heo v (hev ▸ Sym2.mem_mk_right u v)
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  obtain ⟨x, hxv, hux, f, hfo, hfx⟩ := exists_other_outer_neighbor G Q e he heo (hsat u hu).ge
  obtain ⟨y, hyu, hvy, g, hgo, hgy⟩ := exists_other_outer_neighbor G Q e (he.trans Sym2.eq_swap) heo
    (hsat v hv).ge
  have hxP := hOP f hfo x (hfx.symm ▸ Sym2.mem_mk_right u x)
  have hyP := hOP g hgo y (hgy.symm ▸ Sym2.mem_mk_right v y)
  have hxy : x ≠ y := by
    intro hxy
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by rw [ht2 x hxP]; omega)
    have haR : a ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ ha
    rcases mem_union.mp (outer_edge_types_cover_root_labels G Q hQ r e he heo haR) with hau | hav
    · exact disjoint_left.mp (disjoint_types f hfx hfo) hau ha
    · exact disjoint_left.mp (disjoint_types g hgy hgo) hav (hxy ▸ ha)
  have hPeq : P = {u, v, x, y} := by
    apply (eq_of_subset_of_card_le ?_ ?_).symm
    · intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption
    · have hun : u ∉ ({v, x, y} : Finset V) := by simp [huv.ne, hux.ne, hyu.symm]
      have hvn : v ∉ ({x, y} : Finset V) := by simp [hxv.symm, hvy.ne]
      simpa only [card_insert_of_notMem hun, card_insert_of_notMem hvn, card_pair hxy] using hPc
  have hex : ∃ k ∈ O, u ∉ k.val ∧ v ∉ k.val := by
    have hcu := card_union_add_card_inter (edgeIncidences G O u) (edgeIncidences G O v)
    have hpos : 0 < (edgeIncidences G O u ∩ edgeIncidences G O v).card := card_pos.mpr
      ⟨e, mem_inter.mpr ⟨mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_left u v⟩,
        mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_right u v⟩⟩⟩
    have hs : ¬ O ⊆ edgeIncidences G O u ∪ edgeIncidences G O v := by
      intro hs
      have hb := card_le_card hs
      have hsu := hsat u hu
      have hsv := hsat v hv
      change O.card = 4 at ho
      omega
    obtain ⟨k, hk, hkn⟩ := not_subset.mp hs
    exact ⟨k, hk, fun h => hkn (mem_union_left _ (mem_filter.mpr ⟨hk, h⟩)),
      fun h => hkn (mem_union_right _ (mem_filter.mpr ⟨hk, h⟩))⟩
  obtain ⟨k, hko, hku, hkv⟩ := hex
  have hxN : x ∉ G.neighborFinset r := fun h =>
    (outerEdges_endpoints G Q r f hfx hfo).2.2.2.2 ((G.mem_neighborFinset r x).mp h)
  have hyN : y ∉ G.neighborFinset r := fun h =>
    (outerEdges_endpoints G Q r g hgy hgo).2.2.2.2 ((G.mem_neighborFinset r y).mp h)
  have hxC : x ∈ endpointNeighbourCover G u v :=
    mem_union_left _ (mem_erase.mpr ⟨hxv, (G.mem_neighborFinset u x).mpr hux⟩)
  have hyC : y ∈ endpointNeighbourCover G u v :=
    mem_union_right _ (mem_erase.mpr ⟨hyu, (G.mem_neighborFinset v y).mpr hvy⟩)
  have hkC : k ∈ edgesInside G univ (endpointNeighbourCover G u v) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro a ha
    have hp := hOP k hko a ha
    simp only [hPeq, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (hku ha).elim
    · exact (hkv ha).elim
    · exact hxC
    · exact hyC
  have hb := two_type_stars_inside_add_external_edge G hxy hxN hyN (endpointNeighbourCover G u v)
    hxC hyC (outer_root_neighborhood_subset_cover G hΔ Q hQ hR e he heo) k hkC
    (fun a ha hn => (mem_filter.mp hko).2.2 a ha ((G.mem_neighborFinset r a).mp hn))
  have hcx := ht2 x hxP
  have hcy := ht2 y hyP
  have hi := conflict_degree_add_inside_le_sum G e he
  have hsum := sum_le_sum (s := endpointNeighbourCover G u v) (fun a _ => hΔ a)
  have hc := endpointNeighbourCover_card_le_six G huv hΔ
  have he20 := h20 e (mem_filter.mp heo).1
  simp only [sum_const, smul_eq_mul] at hsum
  omega

end StrongEdge19
