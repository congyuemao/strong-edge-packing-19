module

public import StrongEdge19.QuadLoad
public import StrongEdge19.BipartiteSupport
public import StrongEdge.Bounds.TwentyCliqueRigidity

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high19_large_quad_outer_supported
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4)
    (hzr : z ≠ r) (hz : (rootType G r z).card = 4) :
    ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ (multipleTips G r).erase z := by
  have hsmall := high19_large_quad_other_types_le_two G hΔ Q hQ h19 hq hR hzr hz
  have hiz := outer_incidence_add_type_card_le_degree G Q r z
  have hdz := hΔ z
  have hno : ∀ e ∈ outerEdges G Q r, z ∉ e.val := by
    intro e he hze
    have hp : 0 < (edgeIncidences G (outerEdges G Q r) z).card :=
      card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hze⟩⟩
    omega
  intro e heo
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ w : Sym2 V, w = e.val from ⟨e.val, rfl⟩)
  have ends := outerEdges_endpoints G Q r e hev.symm heo
  have huz : u ≠ z := fun h => hno e heo (hev ▸ h ▸ Sym2.mem_mk_left u v)
  have hvz : v ≠ z := fun h => hno e heo (hev ▸ h ▸ Sym2.mem_mk_right u v)
  have hu := hsmall u ends.2.1 huz
  have hv := hsmall v ends.2.2.1 hvz
  have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
    (card_union_le _ _)
  rw [← hev, Sym2.forall_mem_pair]
  exact ⟨mem_erase.mpr ⟨huz, mem_filter.mpr ⟨mem_univ _, ends.2.1, by omega⟩⟩,
    mem_erase.mpr ⟨hvz, mem_filter.mpr ⟨mem_univ _, ends.2.2.1, by omega⟩⟩⟩

/-- The original quadruple core has four double tips and uses all twelve type incidences. -/
theorem high19_large_quad_counts
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4)
    (hzr : z ≠ r) (hz : (rootType G r z).card = 4) :
    (multipleTips G r).card = 5 ∧
      (∑ x ∈ multipleTips G r, (rootType G r x).card) = 12 ∧
      3 ≤ (outerEdges G Q r).card ∧ (outerEdges G Q r).card ≤ 4 := by
  let P := multipleTips G r
  let D := P.erase z
  have hzP : z ∈ P := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
  have he := sum_erase_add P (fun x => (rootType G r x).card) hzP
  have hc := card_erase_add_one hzP
  have hs := sum_le_sum (s := D)
    (fun x hx => (mem_filter.mp (mem_erase.mp hx).2).2.2)
  simp only [sum_const, smul_eq_mul] at hs
  have hb := multipleTips_type_sum_le_twelve G hΔ r
  change (∑ x ∈ P, (rootType G r x).card) ≤ 12 at hb
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun a _ => (edgeIncidences_card_le_degree G Q a).trans (hΔ a))
  have htotal := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hlo : 3 ≤ (outerEdges G Q r).card := by omega
  have hsmall := high19_large_quad_other_types_le_two G hΔ Q hQ h19 hq hR hzr hz
  have hD := high19_large_quad_outer_supported G hΔ Q hQ h19 hq hR hzr hz
  have hD4 : D.card = 4 := by
    have hd4 : D.card ≤ 4 := by change _ + _ = _ at he; change _ + 1 = _ at hc; dsimp [D] at hs ⊢; omega
    by_contra hn
    have hD3 : D.card ≤ 3 := by omega
    have ho := small_complementary_types_outer_card_le_two G Q hQ r hR D hD3 hD (by
      intro x hx
      exact hsmall x (mem_filter.mp (mem_erase.mp hx).2).2.1 (mem_erase.mp hx).1)
    omega
  have hO := outer_card_add_quad_tips_le_multipleTips G hΔ Q hQ r hR {z} (by
    intro x hx
    have h : x = z := mem_singleton.mp hx
    subst x
    exact ⟨hzr, by omega⟩)
  simp only [card_singleton] at hO
  change _ + 1 ≤ P.card at hO
  change P.card = 5 ∧ (∑ x ∈ P, (rootType G r x).card) = 12 ∧ _
  change D.card + 1 = P.card at hc
  change (∑ x ∈ D, (rootType G r x).card) + _ = _ at he
  omega

theorem high19_large_quad_positive_type_support
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4)
    (hzr : z ≠ r) (hz : (rootType G r z).card = 4) :
    ∀ x, x ≠ r → 0 < (rootType G r x).card → x ∈ multipleTips G r := by
  have hsum := (high19_large_quad_counts G hΔ Q hQ h19 hq hR hzr hz).2.1
  intro x hxr hx
  by_contra hxp
  have hr : r ∉ insert x (multipleTips G r) := by
    simp only [mem_insert, multipleTips, mem_filter, mem_univ, true_and]
    tauto
  have hb := root_type_sum_le_twelve G hΔ r (insert x (multipleTips G r)) hr
  rw [sum_insert hxp] at hb
  omega

end StrongEdge19
