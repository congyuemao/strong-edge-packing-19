module

public import StrongEdge19.RootLoad
public import StrongEdge.Bounds.TwentyCliqueTypes

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Saturation uses the actual outer-edge count, rather than a fixed threshold. -/
theorem labels_saturated_of_card_ge_sixteen_add_outer
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    (hq : 16 + (outerEdges G Q r).card ≤ Q.card) :
    (∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4) ∧
      ∀ x, rootType G r x ⊆ rootLabels G Q x := by
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  have hA : ∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4 := by
    intro a ha
    have he := sum_erase_add (G.neighborFinset r) (fun a => (edgeIncidences G Q a).card) ha
    have hca := card_erase_add_one ha
    have hs := sum_le_sum (s := (G.neighborFinset r).erase a)
      (fun b _ => (edgeIncidences_card_le_degree G Q b).trans (hΔ b))
    have hda := (edgeIncidences_card_le_degree G Q a).trans (hΔ a)
    simp only [sum_const, smul_eq_mul] at hs
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
    omega
  refine ⟨hA, ?_⟩
  intro x a ha
  have haN := filter_subset _ _ ha
  have hfull : rootLabels G Q a = G.neighborFinset a :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q a) (by
      rw [rootLabels_card, hA a haN, SimpleGraph.card_neighborFinset_eq_degree]
      exact hΔ a)
  apply root_label_mem_symm G Q
  rw [hfull]
  exact (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp ha).2.symm

/-- Saturated independent label neighbourhoods exclude a triple without a quadruple. -/
theorem no_triple_of_saturated_independent_labels
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a))
    (hdA : ∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4)
    (hfull : ∀ x, rootType G r x ⊆ rootLabels G Q x)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 3)
    (hNr : (G.neighborFinset r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) : False := by
  have hsub : ∀ y ∈ multipleTips G r, rootType G r y ⊆ rootType G r x := by
    intro y hy
    obtain ⟨_, hyr, hcy⟩ := mem_filter.mp hy
    rcases full_root_types_nested_or_disjoint G Q hQ hN hA hfull x y with h | h | h
    · exact (eq_of_subset_of_card_le h (by have hb := ht y hyr; omega)).symm.subset
    · exact h
    · obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ hx hcy
      exact (disjoint_left.mp h (mem_inter.mp ha).1 (mem_inter.mp ha).2).elim
  have hx3 : (rootType G r x).card = 3 := by have hc := ht x hxr; omega
  have hmissing : ¬ G.neighborFinset r ⊆ rootType G r x := by
    intro h
    have hc := card_le_card h
    omega
  obtain ⟨b, hbN, hbx⟩ := not_subset.mp hmissing
  have hdb := hdA b hbN
  have hlabels : rootLabels G Q b = G.neighborFinset b :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q b) (by
      rw [rootLabels_card, hdb, SimpleGraph.card_neighborFinset_eq_degree]
      exact hΔ b)
  have hdbG : G.degree b = 4 := by
    have hb := edgeIncidences_card_le_degree G Q b
    have hu := hΔ b
    omega
  have hbroot := (G.mem_neighborFinset r b).mp hbN
  have hs : (G.neighborFinset b).erase r ⊆ G.neighborFinset x \ G.neighborFinset r := by
    intro z hz
    obtain ⟨hzr, hzb⟩ := mem_erase.mp hz
    have hbz := (G.mem_neighborFinset b z).mp hzb
    have hbzt : b ∈ rootType G r z := (mem_rootType G r z b).mpr ⟨hbroot, hbz.symm⟩
    have hzsmall : (rootType G r z).card ≤ 1 := by
      by_contra hn
      have hzP : z ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
      exact hbx (hsub z hzP hbzt)
    have hzT : rootType G r z = {b} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr hbzt) (by simpa using hzsmall)).symm
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by omega)
    have hab : a ≠ b := fun h => hbx (h ▸ ha)
    have haz : a ∉ rootType G r z := by simpa only [hzT, mem_singleton] using hab
    obtain ⟨_, e, heQ, he⟩ := mem_filter.mp (hlabels.symm ▸ hzb)
    obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp (hfull x ha)
    have hzx := root_selected_edges_force_adj G Q hQ hN hbroot
      ((mem_rootType G r x a).mp ha).1 haz hbx e f heQ hfQ he (hf.trans Sym2.eq_swap)
    refine mem_sdiff.mpr ⟨(G.mem_neighborFinset x z).mpr hzx.symm, ?_⟩
    intro hzN
    exact hN hbroot ((G.mem_neighborFinset r z).mp hzN) hbz.ne hbz
  have hc := card_le_card hs
  have hec := card_erase_add_one ((G.mem_neighborFinset b r).mpr hbroot.symm)
  have hr := residual_neighbors_add_type_card G r x
  have hd := hΔ x
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hec
  omega

variable [DecidableRel (conflictGraph G).Adj]

/-- This excludes the three-outer-edge, two-triple branch of Stage 3. -/
theorem high19_large_triple_requires_four_outer_edges
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 3)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) :
    4 ≤ (outerEdges G Q r).card := by
  by_contra hn
  have hN := high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) r hR
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
  exact no_triple_of_saturated_independent_labels G hΔ Q hQ hN hA hdA hfull ht hNr hxr hx

end StrongEdge19
