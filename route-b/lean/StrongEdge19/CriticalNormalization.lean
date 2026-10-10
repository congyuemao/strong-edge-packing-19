module

public import StrongEdge19.Tertiary
public import StrongEdge19.Compensation
public import StrongEdge.Packing195Thresholds

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

section Induced

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]
variable (F : Set W) [DecidablePred (· ∈ F)]

theorem induced_neighborhood_closed_of_degree_eq (v : F)
    (heq : H.degree v.val = (H.induce F).degree v) :
    ∀ x, H.Adj v.val x → x ∈ F := by
  have hc := congrArg Finset.card (H.map_neighborFinset_induce v)
  simp only [card_map, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hs : H.neighborFinset v.val ∩ F.toFinset ⊆ H.neighborFinset v.val := inter_subset_left
  have hi : H.neighborFinset v.val ∩ F.toFinset = H.neighborFinset v.val :=
    eq_of_subset_of_card_le hs (by
      simp only [SimpleGraph.card_neighborFinset_eq_degree]
      omega)
  intro x hx
  have hx' : x ∈ H.neighborFinset v.val ∩ F.toFinset :=
    hi.symm ▸ (H.mem_neighborFinset v.val x).mpr hx
  exact Set.mem_toFinset.mp (mem_inter.mp hx').2

omit [Fintype W] [DecidableRel H.Adj] [DecidablePred (· ∈ F)] in
theorem induced_clique_image (Q : Finset F)
    (hQ : (H.induce F).IsClique (Q : Set F)) :
    H.IsClique (↑(Q.image Subtype.val) : Set W) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
  exact hQ ha hb (fun heq => hxy (congrArg Subtype.val heq))

end Induced

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (F : Set G.edgeSet) [DecidablePred (· ∈ F)]

/-- Exact zero deficit restricts the centre degree to the five critical rows. -/
theorem zero_deficit_degree_range
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsOptimal ((conflictGraph G).induce F) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    19 ≤ ((conflictGraph G).induce F).degree v ∧
      ((conflictGraph G).induce F).degree v ≤ 23 ∧
      (privateFinset ((conflictGraph G).induce F) M v).card =
        38 - ((conflictGraph G).induce F).degree v := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  have hc : H.IsClique (P : Set F) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx) ((mem_privateFinset H M v y).mp hy) hxy
  have hm : ∀ x ∈ P, H.degree v ≤ H.degree x := by
    intro x hx
    exact private_degree_mono H M hM hv ((mem_privateFinset H M v x).mp hx)
  have hp := private_card_le_degree_add_one H M v
  have hd : H.degree v ≤ 24 :=
    (induced_degree_le (conflictGraph G) F v).trans (conflict_degree_le_24 G hΔ v.val)
  have hi : H.degree v + 1 + P.card = 39 := by
    change 39 - ((H.degree v + 1 + P.card : ℕ) : ℤ) = 0 at hzero
    omega
  have h24 : H.degree v ≠ 24 := by
    intro heq
    have hb := clique_bound_induce (conflictGraph G) F 24 13
      (high24_clique_card_le_thirteen G hΔ) P hc (fun x hx => by
        change 24 ≤ H.degree x
        have h := hm x hx
        omega)
    omega
  change 19 ≤ H.degree v ∧ H.degree v ≤ 23 ∧ P.card = 38 - H.degree v
  change H.degree v + 1 ≥ P.card at hp
  omega

/-- The next upstream threshold supplies an exact full-degree witness in a critical private clique. -/
theorem zero_deficit_full_degree_witness
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsOptimal ((conflictGraph G).induce F) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    ∃ x : F, IsPrivate ((conflictGraph G).induce F) M v x ∧
      (conflictGraph G).degree x.val ≤ ((conflictGraph G).induce F).degree v := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  obtain ⟨hlo, hhi, hp⟩ := zero_deficit_degree_range G F hΔ M hM hv hzero
  change 19 ≤ H.degree v at hlo
  change H.degree v ≤ 23 at hhi
  change P.card = 38 - H.degree v at hp
  have hc : H.IsClique (P : Set F) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx) ((mem_privateFinset H M v y).mp hy) hxy
  have hQ := induced_clique_image (conflictGraph G) F P hc
  have hQc : Q.card = P.card := card_image_of_injective P Subtype.val_injective
  by_contra hn
  have hcost : ∀ x ∈ Q, H.degree v + 1 ≤ (conflictGraph G).degree x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have hnot : ¬ (conflictGraph G).degree y.val ≤ H.degree v :=
      fun h => hn ⟨y, (mem_privateFinset H M v y).mp hy, h⟩
    omega
  have hb := cliqueBounds195_of_degree_le_four G hΔ
  by_cases h19 : H.degree v = 19
  · have h := hb.high20 Q hQ (fun x hx => by have h := hcost x hx; omega)
    omega
  by_cases h20 : H.degree v = 20
  · have h := hb.high21 Q hQ (fun x hx => by have h := hcost x hx; omega)
    omega
  by_cases h21 : H.degree v = 21
  · have h := hb.high22 Q hQ (fun x hx => by have h := hcost x hx; omega)
    omega
  by_cases h22 : H.degree v = 22
  · have h := hb.high23 Q hQ (fun x hx => by have h := hcost x hx; omega)
    omega
  have h := high24_clique_card_le_thirteen G hΔ Q hQ (fun x hx => by have h := hcost x hx; omega)
  omega

/-- Tertiary optimization closes the centre's full original conflict neighbourhood. -/
theorem zero_deficit_full_degree_and_closed_neighborhood
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    (conflictGraph G).degree v.val = ((conflictGraph G).induce F).degree v ∧
      ∀ x, (conflictGraph G).Adj v.val x → x ∈ F := by
  obtain ⟨x, hx, hw⟩ := zero_deficit_full_degree_witness G F hΔ M hM.1 hv hzero
  have heq := centre_cost_eq_degree_of_private_witness ((conflictGraph G).induce F)
    (fun e : F => (conflictGraph G).degree e.val)
    (fun e => induced_degree_le (conflictGraph G) F e) M hM hv hx hw
  exact ⟨heq, induced_neighborhood_closed_of_degree_eq (conflictGraph G) F v heq⟩

end StrongEdge19
