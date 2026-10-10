module

public import StrongEdge19.SmallTypes

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high23_clique_card_le_thirteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 13 := by
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    exact high23_root_type_card_le_two G hΔ Q h23 r (by omega) hxr
  have h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e := fun e he => by have h := h23 e he; omega
  have hk := high21_small_types_rootEdges_card_le_eight G hΔ Q hQ h21 hR ht
  have ho := high23_outer_edges_card_le_one_of_root_four G hΔ Q hQ h23 r hR
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  omega

end StrongEdge19
