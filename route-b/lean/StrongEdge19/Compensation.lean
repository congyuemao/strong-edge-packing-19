module

public import StrongEdge.DoubleCount
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Excess multiplicity. Terms at multiplicities one and two are zero. -/
def excessCoverage (M : Finset W) : ℕ := ∑ x : W, ((covering H M x).card - 2)

/-- Integer deficits retain the negative contribution of an exceptional component. -/
noncomputable def deficit (M : Finset W) (e : W) : ℤ :=
  39 - ((H.degree e + 1 + (privateFinset H M e).card : ℕ) : ℤ)

omit [Fintype W] in
theorem privateOwners_card_eq_indicator (M : Finset W) (x : W) :
    (privateOwners H M x).card = if (covering H M x).card = 1 then 1 else 0 := by
  classical
  by_cases hone : (covering H M x).card = 1
  · obtain ⟨v, hv⟩ := card_eq_one.mp hone
    have hvc : v ∈ covering H M x := by simp [hv]
    have hvM := (mem_filter.mp hvc).1
    have hp : privateOwners H M x = {v} := by
      ext w
      simp only [privateOwners, mem_filter, mem_singleton]
      constructor
      · rintro ⟨hwM, hwp⟩
        have hcw := (private_iff_covering_singleton H M hwM).mp hwp
        have hwc : w ∈ covering H M x := by simp [hcw]
        simpa only [hv, mem_singleton] using hwc
      · rintro rfl
        exact ⟨hvM, (private_iff_covering_singleton H M hvM).mpr hv⟩
    simp only [hp, card_singleton, hone, ite_true]
  · have hp : privateOwners H M x = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwM, hwp⟩ := mem_filter.mp hw
      have hcw := (private_iff_covering_singleton H M hwM).mp hwp
      exact hone (by simp [hcw])
    simp only [hp, card_empty, hone, ite_false]

/-- The exact local count, before discarding coverage of multiplicity at least three. -/
theorem coverage_pointwise_exact (M : Finset W) (hM : H.IsMaximumIndepSet M) (x : W) :
    (covering H M x).card + (privateOwners H M x).card =
      2 + ((covering H M x).card - 2) := by
  classical
  obtain ⟨v, hv, hcov⟩ := maximum_covers H M hM x
  have hpos : 0 < (covering H M x).card :=
    card_pos.mpr ⟨v, mem_filter.mpr ⟨hv, hcov⟩⟩
  rw [privateOwners_card_eq_indicator]
  split_ifs <;> omega

/-- Stage 1's exact double-counting identity, for arbitrary finite simple graphs. -/
theorem private_double_count_exact (M : Finset W) (hM : H.IsMaximumIndepSet M) :
    (∑ e ∈ M, (H.degree e + 1 + (privateFinset H M e).card)) =
      2 * Fintype.card W + excessCoverage H M := by
  classical
  have hp := sum_congr (s₁ := (univ : Finset W)) rfl
    (fun x _ => coverage_pointwise_exact H M hM x)
  simp only [sum_add_distrib, sum_covering, sum_privateOwners, sum_const,
    card_univ, smul_eq_mul] at hp
  simpa only [excessCoverage, sum_add_distrib, sum_const, smul_eq_mul,
    Nat.mul_comm] using hp

/-- The compensation identity uses integer subtraction, including before correction. -/
theorem compensation_identity (M : Finset W) (hM : H.IsMaximumIndepSet M) :
    2 * (Fintype.card W : ℤ) = 39 * (M.card : ℤ) -
      (∑ e ∈ M, deficit H M e) - (excessCoverage H M : ℤ) := by
  classical
  have h := private_double_count_exact H M hM
  have hz := congrArg (fun n : ℕ => (n : ℤ)) h
  simp only [deficit, sum_sub_distrib, sum_const, nsmul_eq_mul]
  push_cast at hz ⊢
  linarith

/-- For this maximum independent set, the nineteen bound is exactly the compensation budget. -/
theorem nineteen_bound_iff_compensation (M : Finset W) (hM : H.IsMaximumIndepSet M) :
    Fintype.card W ≤ 19 * M.card ↔
      (M.card : ℤ) ≤ (∑ e ∈ M, deficit H M e) + (excessCoverage H M : ℤ) := by
  have hi := compensation_identity H M hM
  constructor
  · intro h
    have hz : (Fintype.card W : ℤ) ≤ 19 * (M.card : ℤ) := by exact_mod_cast h
    omega
  · intro h
    have hz : (Fintype.card W : ℤ) ≤ 19 * (M.card : ℤ) := by omega
    exact_mod_cast hz

theorem nineteen_bound_of_positive_deficits (M : Finset W) (hM : H.IsMaximumIndepSet M)
    (hδ : ∀ e ∈ M, 1 ≤ deficit H M e) : Fintype.card W ≤ 19 * M.card := by
  apply (nineteen_bound_iff_compensation H M hM).mpr
  have hs := sum_le_sum hδ
  simp only [sum_const, nsmul_eq_mul, mul_one] at hs
  have hr : (0 : ℤ) ≤ (excessCoverage H M : ℤ) := Int.natCast_nonneg _
  omega

end StrongEdge19
