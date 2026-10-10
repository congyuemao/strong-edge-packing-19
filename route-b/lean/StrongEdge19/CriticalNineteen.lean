module

public import StrongEdge19.CriticalNormalization
public import StrongEdge19.NineteenRigidity

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
    (hM : IsOptimal ((conflictGraph G).induce F) M)
    {v : F} (hv : v ∈ M)
    (hzero : deficit ((conflictGraph G).induce F) M v = 0)
    (hd : ((conflictGraph G).induce F).degree v = 19) :
    ∃ T : Finset G.edgeSet, (T : Set G.edgeSet) ⊆ F ∧ T.card = 20 ∧
      (conflictGraph G).IsClique (T : Set G.edgeSet) := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  have hPc : P.card = 19 := by
    change 39 - ((H.degree v + 1 + P.card : ℕ) : ℤ) = 0 at hzero
    change H.degree v = 19 at hd
    omega
  have hQcard : Q.card = 19 := by
    rw [card_image_of_injective P Subtype.val_injective]
    exact hPc
  have hP : H.IsClique (P : Set F) := by
    intro x hx y hy hxy
    exact private_isClique H M v hM.1 hv
      ((mem_privateFinset H M v x).mp hx) ((mem_privateFinset H M v y).mp hy) hxy
  have hQ := induced_clique_image (conflictGraph G) F P hP
  have h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    have hm := private_degree_mono H M hM hv ((mem_privateFinset H M v x).mp hx)
    have hf := induced_degree_le (conflictGraph G) F x
    change H.degree x ≤ _ at hf
    change H.degree v = 19 at hd
    omega
  obtain ⟨T, hQT, hTc, hT⟩ := high19_nineteen_clique_extends_to_twenty G hΔ Q hQ h19 hQcard
  have hvP : v ∈ P := (mem_privateFinset H M v v).mpr (private_centre H M v hM.1 hv)
  have hvT : v.val ∈ T := hQT (mem_image.mpr ⟨v, hvP, rfl⟩)
  have hs : (conflictGraph G).neighborFinset v.val ⊆ T.erase v.val := by
    intro e he
    have hve := ((conflictGraph G).mem_neighborFinset v.val e).mp he
    exact mem_erase.mpr ⟨hve.ne.symm, twenty_clique_conflict_closed G hΔ T hT hTc hvT hve⟩
  have heq : (conflictGraph G).degree v.val = H.degree v := by
    have hc := card_le_card hs
    have ht := card_erase_add_one hvT
    have hi := induced_degree_le (conflictGraph G) F v
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    change H.degree v ≤ (conflictGraph G).degree v.val at hi
    change H.degree v = 19 at hd
    omega
  have hclosed := induced_neighborhood_closed_of_degree_eq (conflictGraph G) F v heq
  refine ⟨T, ?_, hTc, hT⟩
  intro e he
  by_cases hev : e = v.val
  · exact hev.symm ▸ v.property
  exact hclosed e (hT hvT he (Ne.symm hev))

end StrongEdge19
