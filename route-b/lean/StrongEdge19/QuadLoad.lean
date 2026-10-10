module

public import StrongEdge19.QuadType

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- A quadruple, a triple and a third multiple tip exceed the label budget. -/
theorem high19_no_quad_triple_multiple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hfull : rootLabels G Q r = G.neighborFinset r)
    {x y z : V} (hxr : x ≠ r) (hyr : y ≠ r) (hzr : z ≠ r)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : 4 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (hz : 2 ≤ (rootType G r z).card) : False := by
  obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ hy hz
  obtain ⟨hay, haz⟩ := mem_inter.mp ha
  have hxfull : rootType G r x = G.neighborFinset r :=
    eq_of_subset_of_card_le (filter_subset _ _)
      (by have hd := hΔ r; simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hd.trans hx)
  have hax : a ∈ rootType G r x := hxfull.symm ▸ filter_subset _ _ hay
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ hax
  have hb := high19_root_label_budget_five G hΔ Q h19 hN haR
  let N := (G.neighborFinset a).erase r
  have hxN : x ∈ N := mem_erase.mpr ⟨hxr,
    (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hyN : y ∈ N := mem_erase.mpr ⟨hyr,
    (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
  have hzN : z ∈ N := mem_erase.mpr ⟨hzr,
    (G.mem_neighborFinset a z).mpr ((mem_rootType G r z a).mp haz).2.symm⟩
  have hs : ({x, y, z} : Finset V) ⊆ N := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun w => ((rootType G r w).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  have hxn : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  rw [sum_insert hxn, sum_pair hyz] at hsum
  have hcx := card_erase_add_one hax
  have hcy := card_erase_add_one hay
  have hcz := card_erase_add_one haz
  change _ ≤ ∑ w ∈ (G.neighborFinset a).erase r, _ at hsum
  omega

/-- In a large high-nineteen clique, all other original types have size at most two. -/
theorem high19_large_quad_other_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    {r x : V} (hR : (rootLabels G Q r).card = 4)
    (hxr : x ≠ r) (hx : (rootType G r x).card = 4) :
    ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
  have hN := high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) r hR
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun a _ => (edgeIncidences_card_le_degree G Q a).trans (hΔ a))
  have htotal := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have ho := outer_card_add_quad_tips_le_multipleTips G hΔ Q hQ r hR {x} (by
    intro z hz
    have heq : z = x := mem_singleton.mp hz
    subst z
    exact ⟨hxr, by omega⟩)
  simp only [card_singleton] at ho
  have hP : 4 ≤ (multipleTips G r).card := by omega
  intro y hyr hyx
  by_contra hn
  have hex : ∃ z ∈ multipleTips G r, z ≠ x ∧ z ≠ y := by
    by_contra hnz
    have hs : multipleTips G r ⊆ {x, y} := by
      intro z hz
      by_cases hzx : z = x
      · simp [hzx]
      have hzy : z = y := by by_contra h; exact hnz ⟨z, hz, hzx, h⟩
      simp [hzy]
    have hc := card_le_card hs
    rw [card_pair hyx.symm] at hc
    omega
  obtain ⟨z, hz, hzx, hzy⟩ := hex
  obtain ⟨_, hzr, hz2⟩ := mem_filter.mp hz
  exact high19_no_quad_triple_multiple G hΔ Q h19 hN hfull hxr hyr hzr
    hyx.symm hzx.symm hzy.symm (by omega) (by omega) hz2

end StrongEdge19
