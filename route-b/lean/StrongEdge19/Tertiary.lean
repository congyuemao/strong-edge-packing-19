module

public import StrongEdge.PrivateExchange

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The third objective is minimized only after cardinality and candidate degrees. -/
def IsTertiaryOptimal (cost : W → ℕ) (M : Finset W) : Prop :=
  IsOptimal H M ∧ ∀ T : Finset W, IsOptimal H T →
    (∑ e ∈ M, cost e) ≤ ∑ e ∈ T, cost e

omit [DecidableEq W] in
theorem tertiary_optimal_exists (cost : W → ℕ) :
    ∃ M : Finset W, IsTertiaryOptimal H cost M := by
  classical
  let S : Finset (Finset W) := univ.filter (IsOptimal H)
  obtain ⟨M₀, hM₀⟩ := optimal_exists H
  have hS : S.Nonempty := ⟨M₀, mem_filter.mpr ⟨mem_univ _, hM₀⟩⟩
  obtain ⟨M, hM, hmin⟩ := S.exists_min_image (fun T => ∑ e ∈ T, cost e) hS
  exact ⟨M, (mem_filter.mp hM).2, fun T hT => hmin T (mem_filter.mpr ⟨mem_univ _, hT⟩)⟩

/-- A degree-preserving private exchange also preserves secondary optimality. -/
theorem private_swap_optimal (M : Finset W) (hM : IsOptimal H M)
    {v x : W} (hv : v ∈ M) (hx : IsPrivate H M v x)
    (heq : H.degree x = H.degree v) :
    IsOptimal H (insert x (M.erase v)) := by
  classical
  by_cases hxv : x = v
  · subst x
    simpa only [insert_erase hv] using hM
  have hxout : x ∉ M := fun h => (hx.2 x h hxv).1 rfl
  have hxerase : x ∉ M.erase v := fun h => hxout (mem_erase.mp h).2
  have hcard : (insert x (M.erase v)).card = M.card := by
    rw [card_insert_of_notMem hxerase, card_erase_add_one hv]
  have hsum : degreeSum H (insert x (M.erase v)) = degreeSum H M := by
    simp only [degreeSum, sum_insert hxerase, heq]
    exact (sum_erase_add M (fun e => H.degree e) hv).symm ▸ (by omega)
  refine ⟨⟨private_swap_independent H M hM.1.isIndepSet hx, ?_⟩, ?_⟩
  · intro U hU
    rw [hcard]
    exact hM.1.maximum U hU
  · intro T hT
    rw [hsum]
    exact hM.2 T hT

theorem private_cost_mono_of_equal_degree (cost : W → ℕ)
    (M : Finset W) (hM : IsTertiaryOptimal H cost M)
    {v x : W} (hv : v ∈ M) (hx : IsPrivate H M v x)
    (heq : H.degree x = H.degree v) : cost v ≤ cost x := by
  classical
  by_cases hxv : x = v
  · subst x
    exact le_rfl
  have hxout : x ∉ M := fun h => (hx.2 x h hxv).1 rfl
  have hxerase : x ∉ M.erase v := fun h => hxout (mem_erase.mp h).2
  have hT := private_swap_optimal H M hM.1 hv hx heq
  have hmin := hM.2 _ hT
  rw [sum_insert hxerase] at hmin
  have hsum := sum_erase_add M cost hv
  omega

/-- A low-cost private witness normalizes the centre without changing the first objectives. -/
theorem centre_cost_eq_degree_of_private_witness (cost : W → ℕ)
    (hcost : ∀ x, H.degree x ≤ cost x)
    (M : Finset W) (hM : IsTertiaryOptimal H cost M)
    {v x : W} (hv : v ∈ M) (hx : IsPrivate H M v x)
    (hw : cost x ≤ H.degree v) : cost v = H.degree v := by
  have hm := private_degree_mono H M hM.1 hv hx
  have hdx := hcost x
  have heq : H.degree x = H.degree v := by omega
  have hc := private_cost_mono_of_equal_degree H cost M hM hv hx heq
  have hdv := hcost v
  omega

end StrongEdge19
