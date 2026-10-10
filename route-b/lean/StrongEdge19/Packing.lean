module

public import StrongEdge19.PositiveDeficits

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The nineteen bound before restoring fully selected exceptional components. -/
theorem induced_matching_packing19_of_no_twenty_clique
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet)
    (hno : ∀ Q : Finset G.edgeSet, Q ⊆ F →
      (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card := by
  classical
  let S : Set G.edgeSet := F
  let : Fintype S := Subtype.fintype (fun e => e ∈ S)
  let H := (conflictGraph G).induce S
  obtain ⟨N, hN⟩ := tertiary_optimal_exists H (fun e : S => (conflictGraph G).degree e.val)
  have hbudget := global_compensation_of_no_twenty_clique G S hΔ hno N hN
  have hb := (nineteen_bound_iff_compensation H N hN.1.1).mpr hbudget
  refine ⟨N.image Subtype.val, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact a.property
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hf
    exact hN.1.1.isIndepSet ha hb (fun h => hef (congrArg Subtype.val h))
  · have hcardS : Fintype.card S = F.card := Fintype.card_of_subtype F (fun _ => Iff.rfl)
    simpa only [card_image_of_injective N Subtype.val_injective, hcardS] using hb

end StrongEdge19
