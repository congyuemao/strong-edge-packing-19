module

public import StrongEdge19.ClosedCore

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_ten_edges_card_le_twenty
    (hΔ : ∀ x, G.degree x ≤ 4) (S : Finset V) (hS : S.card ≤ 10)
    (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S) :
    (edgesInside G univ S).card ≤ 20 := by
  have heq : edgesMeeting G univ S = edgesInside G univ S := by
    ext e
    simp only [edgesMeeting, edgesInside, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hxS, hxe⟩
      obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
      rw [hey, Sym2.forall_mem_pair]
      exact ⟨hxS, hclosed x hxS ((G.mem_neighborFinset x y).mpr (G.mem_edgeSet.mp (hey ▸ e.property)))⟩
    · intro h
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      exact ⟨u, h u (hev ▸ Sym2.mem_mk_left u v), hev ▸ Sym2.mem_mk_left u v⟩
  have hi := incidence_sum_eq_meeting_add_inside G univ S
  rw [heq] at hi
  simp only [edgeIncidences_univ_card] at hi
  have hb := sum_le_sum (s := S) (fun x _ => hΔ x)
  simp only [sum_const, smul_eq_mul] at hb
  omega

theorem conflict_stays_in_closed_support
    (S : Finset V) (hclosed : ∀ x ∈ S, G.neighborFinset x ⊆ S)
    {e f : G.edgeSet} (he : ∀ x ∈ e.val, x ∈ S)
    (hef : (conflictGraph G).Adj e f) : f ∈ edgesInside G univ S := by
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hu := he u (hev ▸ Sym2.mem_mk_left u v)
  have hv := he v (hev ▸ Sym2.mem_mk_right u v)
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G hev.symm hef
  have hwS : w ∈ S := by
    rcases mem_union.mp hw with h | h
    · exact hclosed u hu (mem_erase.mp h).2
    · exact hclosed v hv (mem_erase.mp h).2
  obtain ⟨x, hfx⟩ := Sym2.mem_iff_exists.mp hwf
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rw [hfx, Sym2.forall_mem_pair]
  exact ⟨hwS, hclosed w hwS ((G.mem_neighborFinset w x).mpr (G.mem_edgeSet.mp (hfx ▸ f.property)))⟩

variable [DecidableRel (conflictGraph G).Adj]

/-- The complete extension lies in the original graph; candidate membership is not assumed. -/
theorem high19_nineteen_clique_extends_to_twenty
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : Q.card = 19) :
    ∃ T : Finset G.edgeSet, Q ⊆ T ∧ T.card = 20 ∧
      (conflictGraph G).IsClique (T : Set G.edgeSet) := by
  obtain ⟨S, hS, hsupport, hclosed⟩ :=
    high19_large_clique_closed_ten_support G hΔ Q hQ h19 (by omega)
  let T := edgesInside G univ S
  have hT20 : T.card ≤ 20 := closed_ten_edges_card_le_twenty G hΔ S hS hclosed
  have hQT : Q ⊆ T := fun e he => mem_filter.mpr ⟨mem_univ _, hsupport e he⟩
  have hneigh : ∀ e ∈ Q, (conflictGraph G).neighborFinset e = T.erase e := by
    intro e he
    have hs : (conflictGraph G).neighborFinset e ⊆ T.erase e := by
      intro f hf
      have hef := ((conflictGraph G).mem_neighborFinset e f).mp hf
      exact mem_erase.mpr ⟨hef.ne.symm, conflict_stays_in_closed_support G S hclosed (hsupport e he) hef⟩
    apply eq_of_subset_of_card_le hs
    have hc := card_erase_add_one (hQT he)
    have hd := h19 e he
    simp only [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < Q.card by omega)
  have hTc : T.card = 20 := by
    have hc := congrArg Finset.card (hneigh e he)
    have hec := card_erase_add_one (hQT he)
    have hd := h19 e he
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  have hrest : (T \ Q).card ≤ 1 := by
    have hc := card_sdiff_add_card_eq_card hQT
    omega
  refine ⟨T, hQT, hTc, ?_⟩
  intro a ha b hb hab
  by_cases haQ : a ∈ Q
  · apply ((conflictGraph G).mem_neighborFinset a b).mp
    rw [hneigh a haQ]
    exact mem_erase.mpr ⟨hab.symm, hb⟩
  by_cases hbQ : b ∈ Q
  · apply SimpleGraph.Adj.symm
    apply ((conflictGraph G).mem_neighborFinset b a).mp
    rw [hneigh b hbQ]
    exact mem_erase.mpr ⟨hab, ha⟩
  exact (hab (card_le_one.mp hrest a (mem_sdiff.mpr ⟨ha, haQ⟩) b (mem_sdiff.mpr ⟨hb, hbQ⟩))).elim

/-- Stage 3 rigidity: the nineteen-clique is contained in a whole original doubled five-cycle. -/
theorem high19_nineteen_clique_in_five_cycle_blowup
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h19 : ∀ e ∈ Q, 19 ≤ (conflictGraph G).degree e) (hq : Q.card = 19) :
    ∃ T : Finset G.edgeSet, Q ⊆ T ∧ T.card = 20 ∧
      (conflictGraph G).IsClique (T : Set G.edgeSet) ∧
      IsFiveCycleBlowupComponent G (selectedSupport G T) := by
  obtain ⟨T, hQT, hTc, hT⟩ := high19_nineteen_clique_extends_to_twenty G hΔ Q hQ h19 hq
  exact ⟨T, hQT, hTc, hT, twenty_clique_support_is_five_cycle_blowup G hΔ T hT hTc⟩

end StrongEdge19
