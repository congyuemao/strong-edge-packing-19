module

public import StrongEdge19.OuterSupport

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- A large clique at full threshold nineteen has a quadruple root type. -/
theorem high19_large_clique_exists_type_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : 19 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    ∃ z, z ≠ r ∧ (rootType G r z).card = 4 := by
  by_contra hn
  have hN := high19_large_clique_root_neighborhood_independent G hΔ Q hQ h19 (by omega) r hR
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 3 := by
    intro x hxr
    have hb := card_le_card (show rootType G r x ⊆ G.neighborFinset r from filter_subset _ _)
    have hd := hΔ r
    have hne : (rootType G r x).card ≠ 4 := fun h => hn ⟨x, hxr, h⟩
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hb
    omega
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    by_cases htwo : ∃ y, y ≠ r ∧ y ≠ x ∧ 3 ≤ (rootType G r y).card
    · obtain ⟨y, hyr, hyx, hy⟩ := htwo
      have hlo := high19_large_triple_requires_four_outer_edges G hΔ Q hQ h19 hq r hR ht hxr hx
      have hhi := high19_two_triples_outer_card_le_three G hΔ Q hQ h19 hN hR hxr hyr hyx.symm hx hy
      omega
    · have hsmall : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
        intro y hyr hyx
        have hn3 : ¬ 3 ≤ (rootType G r y).card := fun h => htwo ⟨y, hyr, hyx, h⟩
        omega
      have hc := clique_card_le_eighteen_of_unique_triple G hΔ Q hQ hN hR hxr
        (by have hb := ht x hxr; omega) hsmall
      omega
  · have hsmall : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
      intro x hxr
      have hn3 : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
      omega
    have hc := clique_card_le_eighteen_of_independent_root_types_le_two G hΔ Q hQ r hR hN hsmall
    omega

end StrongEdge19
