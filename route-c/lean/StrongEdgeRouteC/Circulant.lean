module

public import StrongEdge.Conflict
public import StrongEdge.Bounds.TwentyCliqueParts

@[expose] public section

/-!
# The circulant `C₉(1,3)` (Route C, Proposition 1.1)

All eighteen edges of the 4-regular circulant `C₉(1,3)` pairwise conflict in the original graph.
Hence every induced matching has at most one edge, so `ν_s = 1 = m / 18`. The graph has no
component isomorphic to `C₅[2]`, because it has only nine vertices. It therefore refutes the
conjectured bound `ν_s ≥ m / 17` for graphs of maximum degree at most four without such
components (Joos, arXiv:1407.8336v1, Conjecture 2), and it attains the whole-edge-set bound
`m ≤ 18 ν_s`.

Finite evaluations use kernel-checked `decide`, not `native_decide`.
-/

namespace StrongEdgeRouteC

open Finset StrongEdge

set_option synthInstance.maxSize 1000

/-- Adjacency of `C₉(1,3)`: the difference of the endpoints is `±1` or `±3` modulo nine. -/
def circulantAdj (x y : Fin 9) : Prop :=
  x - y = 1 ∨ y - x = 1 ∨ x - y = 3 ∨ y - x = 3

instance : DecidableRel circulantAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem circulantAdj_symm : ∀ x y : Fin 9, circulantAdj x y → circulantAdj y x := by
  decide

theorem circulantAdj_irrefl : ∀ x : Fin 9, ¬ circulantAdj x x := by
  decide

/-- The circulant graph `C₉(1,3)` on `Fin 9`. -/
def circulant913 : SimpleGraph (Fin 9) where
  Adj := circulantAdj
  symm := ⟨fun x y h => circulantAdj_symm x y h⟩
  loopless := ⟨fun x h => circulantAdj_irrefl x h⟩

instance : DecidableRel circulant913.Adj := fun x y =>
  inferInstanceAs (Decidable (circulantAdj x y))

/-- `C₉(1,3)` is 4-regular, so its maximum degree is four. -/
theorem circulant913_degree_four : ∀ x, circulant913.degree x = 4 := by
  decide

theorem circulant913_edge_count : (univ : Finset circulant913.edgeSet).card = 18 := by
  decide

/-- Proposition 1.1: any two distinct edges of `C₉(1,3)` conflict in the original graph. -/
theorem circulant913_all_edges_strong_clique :
    (conflictGraph circulant913).IsClique (Set.univ : Set circulant913.edgeSet) := by
  intro e _ f _ hef
  change StrongConflict circulant913 e f
  have h : ∀ e f : circulant913.edgeSet, e ≠ f → StrongConflict circulant913 e f := by
    simp only [StrongConflict, SimpleGraph.lineGraph_adj_iff_exists]
    decide
  exact h e f hef

/-- Every induced matching of `C₉(1,3)` has at most one edge. -/
theorem circulant913_induced_matching_card_le_one (M : Finset circulant913.edgeSet)
    (hM : IsInducedMatching circulant913 (M : Set circulant913.edgeSet)) : M.card ≤ 1 := by
  apply card_le_one.mpr
  intro e he f hf
  by_contra hef
  exact hM he hf hef
    (circulant913_all_edges_strong_clique (Set.mem_univ _) (Set.mem_univ _) hef)

/-- A single edge is an induced matching, so the induced matching number is exactly one. -/
theorem circulant913_exists_induced_matching_card_one :
    ∃ M : Finset circulant913.edgeSet,
      IsInducedMatching circulant913 (M : Set circulant913.edgeSet) ∧ M.card = 1 := by
  have h01 : circulant913.Adj 0 1 := by decide
  refine ⟨{⟨s(0, 1), h01⟩}, ?_, card_singleton _⟩
  intro e he f hf hef
  simp only [coe_singleton, Set.mem_singleton_iff] at he hf
  exact absurd (he.trans hf.symm) hef

/-- `C₉(1,3)` has no component isomorphic to `C₅[2]`: such a component has ten vertices. -/
theorem circulant913_no_five_cycle_blowup_component (S : Finset (Fin 9)) :
    ¬ IsFiveCycleBlowupComponent circulant913 S := by
  rintro ⟨B, A, X, Y, C, hB, hA, hX, hY, hC, hdisj, hS, -⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, implies_true, List.Pairwise.nil, and_true, or_false, forall_eq] at hdisj
  obtain ⟨⟨hBA, hBX, hBY, hBC⟩, ⟨hAX, hAY, hAC⟩, ⟨hXY, hXC⟩, hYC⟩ := hdisj
  have h2 : (B ∪ A).card = 4 := by
    rw [card_union_of_disjoint hBA]; omega
  have h3 : (B ∪ A ∪ X).card = 6 := by
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hBX, hAX⟩)]; omega
  have h4 : (B ∪ A ∪ X ∪ Y).card = 8 := by
    rw [card_union_of_disjoint
      (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hBY, hAY⟩, hXY⟩)]; omega
  have h5 : (B ∪ A ∪ X ∪ Y ∪ C).card = 10 := by
    rw [card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨hBC, hAC⟩, hXC⟩, hYC⟩)]; omega
  have hle := card_le_univ (B ∪ A ∪ X ∪ Y ∪ C)
  simp only [Fintype.card_fin] at hle
  omega

/-- Proposition 1.1, refutation of the `m / 17` conjecture: `C₉(1,3)` has maximum degree four
and no `C₅[2]` component, yet every induced matching `M` satisfies `17 |M| < m`. -/
theorem circulant913_refutes_m_div_17 :
    (∀ x, circulant913.degree x ≤ 4) ∧
      (∀ S : Finset (Fin 9), ¬ IsFiveCycleBlowupComponent circulant913 S) ∧
      ∀ M : Finset circulant913.edgeSet,
        IsInducedMatching circulant913 (M : Set circulant913.edgeSet) →
          17 * M.card < (univ : Finset circulant913.edgeSet).card := by
  refine ⟨fun x => (circulant913_degree_four x).le,
    circulant913_no_five_cycle_blowup_component, fun M hM => ?_⟩
  have := circulant913_induced_matching_card_le_one M hM
  rw [circulant913_edge_count]
  omega

/-- Sharpness of the whole-edge-set eighteen bound: `m = 18 ν_s` for `C₉(1,3)`. -/
theorem circulant913_eighteen_bound_attained :
    ∃ M : Finset circulant913.edgeSet,
      IsInducedMatching circulant913 (M : Set circulant913.edgeSet) ∧
        (univ : Finset circulant913.edgeSet).card = 18 * M.card ∧
        ∀ M' : Finset circulant913.edgeSet,
          IsInducedMatching circulant913 (M' : Set circulant913.edgeSet) → M'.card ≤ M.card := by
  obtain ⟨M, hM, hcard⟩ := circulant913_exists_induced_matching_card_one
  refine ⟨M, hM, by rw [circulant913_edge_count, hcard], fun M' hM' => ?_⟩
  rw [hcard]
  exact circulant913_induced_matching_card_le_one M' hM'

end StrongEdgeRouteC
