module

public import StrongEdge19.CriticalHighDegree
public import StrongEdge19.CriticalNineteen

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (F : Set G.edgeSet) [DecidablePred (· ∈ F)]

/-- Every critical row is impossible once fully selected twenty-cliques are excluded. -/
theorem zero_deficit_impossible
    (hΔ : ∀ x, G.degree x ≤ 4)
    (hno : ∀ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F →
      (conflictGraph G).IsClique (T : Set G.edgeSet) → T.card ≤ 19)
    (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) : False := by
  have hd := zero_deficit_candidate_degree_eq_nineteen G F hΔ M hM hv hzero
  obtain ⟨T, hTF, hTc, hT⟩ := critical_degree_nineteen_forces_selected_twenty G F hΔ M hM.1 hv hzero hd
  have hb := hno T hTF hT
  omega

/-- Tertiary optimality gives the stronger pointwise compensation, one unit at every centre. -/
theorem deficit_pos_of_no_twenty_clique
    (hΔ : ∀ x, G.degree x ≤ 4)
    (hno : ∀ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F →
      (conflictGraph G).IsClique (T : Set G.edgeSet) → T.card ≤ 19)
    (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M) : 1 ≤ deficit ((conflictGraph G).induce F) M v := by
  classical
  let H := (conflictGraph G).induce F
  have hnoH : ∀ T : Finset F, H.IsClique (T : Set F) → T.card ≤ 19 := by
    intro T hT
    have hs : (↑(T.image Subtype.val) : Set G.edgeSet) ⊆ F := by
      intro e he
      obtain ⟨a, _, rfl⟩ := mem_image.mp he
      exact a.property
    have hb := hno (T.image Subtype.val) hs (induced_clique_image (conflictGraph G) F T hT)
    simpa only [card_image_of_injective T Subtype.val_injective] using hb
  have hb := local39_of_clique_bounds H
    (fun e => (induced_degree_le (conflictGraph G) F e).trans (conflict_degree_le_24 G hΔ e.val))
    (cliqueBounds195_induce (conflictGraph G) (cliqueBounds195_of_degree_le_four G hΔ) F)
    hnoH M hM.1 hv
  have hn : deficit H M v ≠ 0 := zero_deficit_impossible G F hΔ hno M hM hv
  unfold deficit at hn ⊢
  change 1 ≤ 39 - ((H.degree v + 1 + (privateFinset H M v).card : ℕ) : ℤ)
  omega

/-- The Route B budget follows for every tertiary-optimal maximum independent set. -/
theorem global_compensation_of_no_twenty_clique
    (hΔ : ∀ x, G.degree x ≤ 4)
    (hno : ∀ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F →
      (conflictGraph G).IsClique (T : Set G.edgeSet) → T.card ≤ 19)
    (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M) :
    (M.card : ℤ) ≤ (∑ e ∈ M, deficit ((conflictGraph G).induce F) M e) +
      (excessCoverage ((conflictGraph G).induce F) M : ℤ) := by
  have hs := sum_le_sum (fun e he => deficit_pos_of_no_twenty_clique G F hΔ hno M hM he)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hs
  have hr : (0 : ℤ) ≤ (excessCoverage ((conflictGraph G).induce F) M : ℤ) := Int.natCast_nonneg _
  omega

end StrongEdge19
