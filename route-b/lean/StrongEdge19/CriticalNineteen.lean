module

public import StrongEdge19.CriticalNormalization

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (F : Set G.edgeSet) [DecidablePred (· ∈ F)]

/-- A zero-deficit centre of candidate degree nineteen forces a wholly selected twenty-clique. -/
theorem critical_degree_nineteen_forces_selected_twenty
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0)
    (hd : ((conflictGraph G).induce F).degree v = 19) :
    ∃ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F ∧ T.card = 20 ∧
      (conflictGraph G).IsClique (T : Set G.edgeSet) := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  have hp := (zero_deficit_degree_range G F hΔ M hM.1 hv hzero).2.2
  rw [hd] at hp
  have hPc : P.card = 19 := hp
  have hQcard : Q.card = 19 := by
    rw [card_image_of_injective P Subtype.val_injective]
    exact hPc
  have hP : H.IsClique (P : Set F) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1.1 hv
      ((mem_privateFinset H M v x).mp hx) ((mem_privateFinset H M v y).mp hy) hxy
  have hQ := induced_clique_image (conflictGraph G) F P hP
  have h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have hm := private_degree_mono H M hM.1 hv ((mem_privateFinset H M v x).mp hx)
    have hf := induced_degree_le (conflictGraph G) F x
    change H.degree x ≤ _ at hf
    change H.degree v = 19 at hd
    omega
  obtain ⟨T, hQT, hTc, hT⟩ := high19_nineteen_clique_extends_to_twenty G hΔ Q hQ h19 hQcard
  have hvP : v ∈ P := (mem_privateFinset H M v v).mpr (private_centre H M v hM.1.1 hv)
  have hvT : v.val ∈ T := hQT (mem_image.mpr ⟨v, hvP, rfl⟩)
  have hclosed := (zero_deficit_full_degree_and_closed_neighborhood G F hΔ M hM hv hzero).2
  refine ⟨T, ?_, hTc, hT⟩
  intro e he
  by_cases hev : e = v.val
  · exact hev.symm ▸ v.property
  exact hclosed e (hT hvT he (Ne.symm hev))

/-- Once wholly selected twenty-cliques are excluded, only degrees twenty through twenty-three remain. -/
theorem zero_deficit_remaining_degree_range
    (hΔ : ∀ x, G.degree x ≤ 4)
    (hno : ∀ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F →
      (conflictGraph G).IsClique (T : Set G.edgeSet) → T.card ≤ 19)
    (M : Finset F)
    (hM : IsTertiaryOptimal ((conflictGraph G).induce F)
      (fun e : F => (conflictGraph G).degree e.val) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0) :
    20 ≤ ((conflictGraph G).induce F).degree v ∧
      ((conflictGraph G).induce F).degree v ≤ 23 := by
  obtain ⟨hlo, hhi, _⟩ := zero_deficit_degree_range G F hΔ M hM.1 hv hzero
  have hn : ((conflictGraph G).induce F).degree v ≠ 19 := by
    intro hd
    obtain ⟨T, hTF, hTc, hT⟩ := critical_degree_nineteen_forces_selected_twenty G F hΔ M hM hv hzero hd
    have hc := hno T hTF hT
    omega
  omega

end StrongEdge19
