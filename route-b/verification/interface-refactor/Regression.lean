module

import StrongEdge19

open Finset StrongEdge StrongEdge19

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

-- Preserve the final theorem interfaces without any optimization or clique hypotheses.
example (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card + tightComponentCount G F :=
  induced_matching_packing19_unconditional G hDelta F

example (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card + (tightComponentsIn G F).card :=
  induced_matching_packing19_with_connected_component_count G hDelta F

example (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    F.card ≤ 19 * ((conflictGraph G).induce (F : Set G.edgeSet)).indepNum +
      (tightComponentsIn G F).card := prescribed_edge_bound19 G hDelta F

example (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet)
    (hzero : tightComponentCount G F = 0) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card := induced_matching_packing19_of_no_full_tight_component G hDelta F hzero

-- The unchanged definitions retain every original connecting edge and the literal correction.
example (e f : G.edgeSet) : StrongConflict G e f ↔
    e ≠ f ∧ (G.lineGraph.Adj e f ∨
      ∃ g : G.edgeSet, G.lineGraph.Adj e g ∧ G.lineGraph.Adj g f) := Iff.rfl

example (S : Set G.edgeSet) :
    IsInducedMatching G S ↔ S.Pairwise (fun e f => ¬ StrongConflict G e f) := Iff.rfl

example (F : Finset G.edgeSet) (c : G.ConnectedComponent) :
    c ∈ tightComponentsIn G F ↔ IsFiveCycleBlowupComponent G (componentVertices G c) ∧
      edgesInside G univ (componentVertices G c) ⊆ F := mem_tightComponentsIn G F c

#print axioms StrongEdge19.induced_matching_packing19_unconditional
#print axioms StrongEdge19.induced_matching_packing19_with_connected_component_count
#print axioms StrongEdge19.prescribed_edge_bound19
#print axioms StrongEdge19.induced_matching_packing19_of_no_full_tight_component
