module

public import StrongEdge19.Packing
public import StrongEdge.TightComponents

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- Restore the upstream isolated twenty-cliques, paying one correction unit per component. -/
theorem induced_matching_packing19_with_twenty_clique_count
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card + (twentyCliquesIn G F).card := by
  classical
  refine Finset.strongInductionOn F fun F ih => ?_
  ·
    by_cases hex : ∃ Q : Finset G.edgeSet, Q ⊆ F ∧ Q.card = 20 ∧
        (conflictGraph G).IsClique (Q : Set G.edgeSet)
    · obtain ⟨Q, hQF, hq, hQ⟩ := hex
      have hQne : Q.Nonempty := card_pos.mp (by omega)
      obtain ⟨M, hMF, hM, hbound⟩ := ih (F \ Q) (sdiff_ssubset hQF hQne)
      obtain ⟨e, heQ⟩ := hQne
      have heM : e ∉ M := fun h => (mem_sdiff.mp (hMF h)).2 heQ
      have hcross : ∀ f ∈ M, ¬ StrongConflict G e f := by
        intro f hf hconf
        exact (mem_sdiff.mp (hMF hf)).2 (twenty_clique_conflict_closed G hΔ Q hQ hq heQ hconf)
      refine ⟨insert e M, ?_, ?_, ?_⟩
      · intro f hf
        rcases mem_insert.mp hf with h | h
        · exact h ▸ hQF heQ
        · exact (mem_sdiff.mp (hMF h)).1
      · intro a ha b hb hab
        rcases mem_insert.mp ha with ha | ha
        · subst a
          rcases mem_insert.mp hb with hb | hb
          · exact (hab hb.symm).elim
          · exact hcross b hb
        · rcases mem_insert.mp hb with hb | hb
          · subst b
            exact fun h => hcross a ha (strongConflict_symm G h)
          · exact hM ha hb hab
      · have hFcard := card_sdiff_add_card_eq_card hQF
        have hcount := card_erase_add_one ((mem_twentyCliquesIn G F Q).mpr ⟨hQF, hq, hQ⟩)
        rw [← twentyCliquesIn_sdiff G hΔ F Q hQF hq hQ] at hcount
        rw [card_insert_of_notMem heM]
        omega
    · have hno : ∀ Q : Finset G.edgeSet, Q ⊆ F →
          (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19 := by
        intro Q hQF hQ
        have hc := clique_card_le_twenty G hΔ Q hQ
        have hn : Q.card ≠ 20 := fun h => hex ⟨Q, hQF, h, hQ⟩
        omega
      obtain ⟨M, hMF, hM, hb⟩ := induced_matching_packing19_of_no_twenty_clique G hΔ F hno
      exact ⟨M, hMF, hM, by omega⟩

/-- Corrected nineteen packing for every candidate set in a graph of maximum degree four. -/
theorem induced_matching_packing19_unconditional
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card + tightComponentCount G F := by
  obtain ⟨M, hMF, hM, hb⟩ := induced_matching_packing19_with_twenty_clique_count G hΔ F
  have hc := twenty_clique_count_le_tight_component_count G hΔ F
  exact ⟨M, hMF, hM, by omega⟩

/-- The correction counts actual original C5[2] connected components whose twenty edges are selected. -/
theorem induced_matching_packing19_with_connected_component_count
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card + (tightComponentsIn G F).card := by
  rw [← tightComponentCount_eq_connected_component_count G F]
  exact induced_matching_packing19_unconditional G hΔ F

theorem induced_matching_packing19_of_no_full_tight_component
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet)
    (hzero : tightComponentCount G F = 0) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 19 * M.card := by
  simpa only [hzero, Nat.add_zero] using induced_matching_packing19_unconditional G hΔ F

/-- The prescribed-edge statement using mathlib's independence number of the full-original conflict graph. -/
theorem prescribed_edge_bound19
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    F.card ≤ 19 * ((conflictGraph G).induce (F : Set G.edgeSet)).indepNum +
      (tightComponentsIn G F).card := by
  classical
  obtain ⟨M, hMF, hM, hb⟩ := induced_matching_packing19_with_connected_component_count G hΔ F
  let S : Set G.edgeSet := F
  let lift : {e // e ∈ M} → S := fun e => ⟨e.val, hMF e.property⟩
  let N := M.attach.image lift
  have hinj : Function.Injective lift := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun e : S => e.val) h
  have hc : N.card = M.card := by
    rw [card_image_of_injective M.attach hinj, card_attach]
  have hN : ((conflictGraph G).induce S).IsIndepSet (N : Set S) := by
    intro a ha b hb hab
    obtain ⟨e, _, rfl⟩ := mem_image.mp ha
    obtain ⟨f, _, rfl⟩ := mem_image.mp hb
    exact hM e.property f.property (fun h => hab (Subtype.ext h))
  have hi := hN.card_le_indepNum
  rw [hc] at hi
  change M.card ≤ ((conflictGraph G).induce (F : Set G.edgeSet)).indepNum at hi
  omega

/-- In particular, the proposed thirty-nine-edge, matching-number-two obstruction cannot occur. -/
theorem candidate_card_le_thirty_eight_of_indepNum_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet)
    (hzero : (tightComponentsIn G F).card = 0)
    (hsmall : ((conflictGraph G).induce (F : Set G.edgeSet)).indepNum ≤ 2) :
    F.card ≤ 38 := by
  have hb := prescribed_edge_bound19 G hΔ F
  omega

end StrongEdge19
