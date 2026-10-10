module

public import StrongEdge.Bounds.TwentyCliqueRoot

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

omit [DecidableRel (conflictGraph G).Adj] in
/-- The selected-subcubic theorem supplies a four-edge root already at eighteen. -/
theorem large_clique_exists_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 18 ≤ Q.card) :
    ∃ r, (rootLabels G Q r).card = 4 := by
  by_contra hn
  have hd : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hx : (edgeIncidences G Q x).card ≠ 4 := fun h =>
      hn ⟨x, by rw [rootLabels_card]; exact h⟩
    omega
  have hc := clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ hd
  omega

/-- At a triangle label, external multiple tips inject into internal cover edges. -/
theorem high19_triangle_external_multiple_card_le_one
    (hΔ : ∀ x, G.degree x ≤ 4) {r a b : V} (e : G.edgeSet)
    (he : e.val = s(r, a)) (h19 : 19 ≤ (conflictGraph G).degree e)
    (hrb : G.Adj r b) (hab : G.Adj a b) :
    (univ.filter (fun x => x ≠ r ∧ ¬ G.Adj r x ∧
      a ∈ rootType G r x ∧ 2 ≤ (rootType G r x).card)).card ≤ 1 := by
  have hb := high19_triangle_cover_inside_card_le_one G hΔ e he h19 hrb hab
  apply le_trans ?_ hb
  apply card_le_via_relation _ _ (fun x f =>
    ∃ c ∈ (rootType G r x).erase a, f.val = s(c, x))
  · intro x hx
    obtain ⟨_, hxr, hxn, hax, hxcard⟩ := mem_filter.mp hx
    have hce := card_erase_add_one hax
    obtain ⟨c, hc⟩ := card_pos.mp (show 0 < ((rootType G r x).erase a).card by omega)
    obtain ⟨hca, hcT⟩ := mem_erase.mp hc
    have hcx := (mem_rootType G r x c).mp hcT
    have hxa := (mem_rootType G r x a).mp hax
    refine ⟨⟨s(c, x), hcx.2.symm⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩,
      c, hc, rfl⟩
    exact Sym2.forall_mem_pair.mpr
      ⟨mem_union_left _ (mem_erase.mpr ⟨hca, (G.mem_neighborFinset r c).mpr hcx.1⟩),
       mem_union_right _ (mem_erase.mpr ⟨hxr, (G.mem_neighborFinset a x).mpr hxa.2.symm⟩)⟩
  · intro x hx y hy f hxf hyf
    obtain ⟨c, hc, hcf⟩ := hxf
    obtain ⟨d, hd, hdf⟩ := hyf
    rcases Sym2.eq_iff.mp (hcf.symm.trans hdf) with h | h
    · exact h.2
    · exact ((mem_filter.mp hx).2.2.1
        (h.2.symm ▸ ((mem_rootType G r y d).mp (mem_erase.mp hd).2).1)).elim

/-- A root triangle leaves at most two selected outer edges at threshold nineteen. -/
theorem high19_root_triangle_outer_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) :
    (outerEdges G Q r).card ≤ 2 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  obtain ⟨_, ea, heaQ, hea⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r a).mpr hra)
  obtain ⟨_, eb, hebQ, heb⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r b).mpr hrb)
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    by_cases hax : a ∈ rootType G r x
    · exact high19_triangle_root_type_card_le_two G hΔ ea hea (h19 ea heaQ) hrb hab hxr hax
    by_cases hbx : b ∈ rootType G r x
    · exact high19_triangle_root_type_card_le_two G hΔ eb heb (h19 eb hebQ) hra hab.symm hxr hbx
    have hs : rootType G r x ⊆ ((G.neighborFinset r).erase a).erase b := by
      intro c hc
      exact mem_erase.mpr ⟨fun h => hbx (h ▸ hc), mem_erase.mpr
        ⟨fun h => hax (h ▸ hc), filter_subset _ _ hc⟩⟩
    have hc := card_le_card hs
    have hca := card_erase_add_one ((G.mem_neighborFinset r a).mpr hra)
    have hcb := card_erase_add_one (mem_erase.mpr
      ⟨hab.ne.symm, (G.mem_neighborFinset r b).mpr hrb⟩)
    have hd := hΔ r
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
    omega
  let P := univ.filter (fun x => x ≠ r ∧ ¬ G.Adj r x ∧
    a ∈ rootType G r x ∧ 2 ≤ (rootType G r x).card)
  have hP : P.card ≤ 1 :=
    high19_triangle_external_multiple_card_le_one G hΔ ea hea (h19 ea heaQ) hrb hab
  have hmeet : ∀ e ∈ outerEdges G Q r, ∃ x ∈ P, x ∈ e.val := by
    intro e heo
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have he := outerEdges_endpoints G Q r e hev.symm heo
    have hcov := outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo
    have hc := (card_le_card hcov).trans (card_union_le _ _)
    have hu := ht u he.2.1
    have hv := ht v he.2.2.1
    have haR := hfull.symm ▸ (G.mem_neighborFinset r a).mpr hra
    rcases mem_union.mp (hcov haR) with hau | hav
    · exact ⟨u, mem_filter.mpr ⟨mem_univ _, he.2.1, he.2.2.2.1, hau, by omega⟩,
        hev ▸ Sym2.mem_mk_left u v⟩
    · exact ⟨v, mem_filter.mpr ⟨mem_univ _, he.2.2.1, he.2.2.2.2, hav, by omega⟩,
        hev ▸ Sym2.mem_mk_right u v⟩
  by_cases hn : (outerEdges G Q r).Nonempty
  · obtain ⟨e, he⟩ := hn
    obtain ⟨x, hx, _⟩ := hmeet e he
    have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x := by
      intro f hf
      obtain ⟨y, hy, hyf⟩ := hmeet f hf
      have hyx : y = x := (card_le_one.mp hP) y hy x hx
      exact mem_filter.mpr ⟨hf, hyx ▸ hyf⟩
    have hc := card_le_card hs
    have hi := outer_incidence_add_type_card_le_degree G Q r x
    have htx := (mem_filter.mp hx).2.2.2.2
    have hd := hΔ x
    omega
  · have he := not_nonempty_iff_eq_empty.mp hn
    simp only [he, card_empty]
    omega

/-- Stage 3, Lemma 2.1: high19 large cliques have independent root neighbourhoods. -/
theorem high19_large_clique_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 18 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb _ hab
  have ho := high19_root_triangle_outer_card_le_two G hΔ Q hQ h19 r hR ha hb hab
  let f : G.edgeSet := ⟨s(a, b), hab⟩
  have hf : f ∈ edgesInside G univ (G.neighborFinset r) := mem_filter.mpr
    ⟨mem_univ _, Sym2.forall_mem_pair.mpr
      ⟨(G.mem_neighborFinset r a).mpr ha, (G.mem_neighborFinset r b).mpr hb⟩⟩
  have hi := card_pos.mpr ⟨f, hf⟩
  have hm := incidence_sum_eq_meeting_add_inside G univ (G.neighborFinset r)
  simp only [edgeIncidences_univ_card] at hm
  have hs := sum_le_sum (s := G.neighborFinset r) (fun x _ => hΔ x)
  have hsub : edgesMeeting G Q (G.neighborFinset r) ⊆ edgesMeeting G univ (G.neighborFinset r) :=
    fun _ he => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩
  have hc := card_le_card hsub
  have hqbound := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  omega

end StrongEdge19
