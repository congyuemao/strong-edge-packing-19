module

public import StrongEdge19.High20Root
public import StrongEdge19.PrivateSubcubic
public import StrongEdge19.High22Root
public import StrongEdge19.High23Root

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (F : Set G.edgeSet) [DecidablePred (· ∈ F)]

/-- Full-neighbourhood closure rules out all three critical degrees above twenty. -/
theorem zero_deficit_degree_le_twenty
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    ((conflictGraph G).induce F).degree v ≤ 20 := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  obtain ⟨hlo, hhi, hp⟩ := zero_deficit_degree_range G F hΔ M hM.1 hv hzero
  obtain ⟨heq, hclosed⟩ := zero_deficit_full_degree_and_closed_neighborhood G F hΔ M hM hv hzero
  change H.degree v ≤ 20
  by_contra hn
  change H.degree v ≤ 23 at hhi
  change P.card = 38 - H.degree v at hp
  change (conflictGraph G).degree v.val = H.degree v at heq
  have hP : H.IsClique (P : Set F) := by
    intro a ha b hb hab
    exact private_isClique H M v hM.1.1 hv ((mem_privateFinset H M v a).mp ha)
      ((mem_privateFinset H M v b).mp hb) hab
  have hQ := induced_clique_image (conflictGraph G) F P hP
  have hQc : Q.card = P.card := card_image_of_injective P Subtype.val_injective
  have hthreshold : ∀ e ∈ Q, H.degree v ≤ (conflictGraph G).degree e := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    exact (private_degree_mono H M hM.1 hv ((mem_privateFinset H M v a).mp ha)).trans
      (induced_degree_le (conflictGraph G) F a)
  have hroot : ∃ r, (rootLabels G Q r).card = 4 := by
    by_contra hnone
    have hd : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
      intro x
      have hu := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
      have hn4 : (edgeIncidences G Q x).card ≠ 4 := fun h => hnone
        ⟨x, by rw [rootLabels_card]; exact h⟩
      omega
    have hb := private_subcubic_card_le_thirteen G F hΔ M hM.1.1 hv hclosed (by omega) hd
    change P.card ≤ 13 at hb
    omega
  obtain ⟨r, hR⟩ := hroot
  by_cases h21 : H.degree v = 21
  · have hb := high21_clique_card_le_sixteen_of_root_four G hΔ Q hQ
      (fun e he => by have h := hthreshold e he; omega) r hR
    omega
  by_cases h22 : H.degree v = 22
  · have hb := high22_clique_card_le_fifteen_of_root_four G hΔ Q hQ
      (fun e he => by have h := hthreshold e he; omega) r hR
    omega
  have hb := high23_clique_card_le_thirteen_of_root_four G hΔ Q hQ
    (fun e he => by have h := hthreshold e he; omega) r hR
  omega

/-- Stage 2 exports only the candidate degree; full-degree normalization is internal to the high-degree case. -/
theorem zero_deficit_candidate_degree_eq_nineteen
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    ((conflictGraph G).induce F).degree v = 19 := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  obtain ⟨hlo, _, hp⟩ := zero_deficit_degree_range G F hΔ M hM.1 hv hzero
  have hhi := zero_deficit_degree_le_twenty G F hΔ M hM hv hzero
  change 19 ≤ H.degree v at hlo
  change H.degree v ≤ 20 at hhi
  by_contra hn
  have hd : H.degree v = 20 := by change H.degree v ≠ 19 at hn; omega
  have hP : H.IsClique (P : Set F) := by
    intro a ha b hb hab
    exact private_isClique H M v hM.1.1 hv ((mem_privateFinset H M v a).mp ha)
      ((mem_privateFinset H M v b).mp hb) hab
  have hb := clique_bound_induce (conflictGraph G) F 20 17
    (high20_clique_card_le_seventeen G hΔ) P hP (fun a ha => by
      have hm := private_degree_mono H M hM.1 hv ((mem_privateFinset H M v a).mp ha)
      change 20 ≤ H.degree a
      omega)
  change P.card = 38 - H.degree v at hp
  omega

end StrongEdge19
