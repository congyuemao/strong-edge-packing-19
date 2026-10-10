module

public import StrongEdge19.CriticalNormalization
public import StrongEdge19.EndpointConflict

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (F : Set G.edgeSet) [DecidablePred (· ∈ F)]

/-- A missing private edge at a closed centre endpoint leaves its other endpoint unused. -/
theorem private_missing_edge_zero_incidence
    (M : Finset F) (hM : ((conflictGraph G).induce F).IsMaximumIndepSet M)
    {v : F} (hv : v ∈ M)
    (hclosed : ∀ f, (conflictGraph G).Adj v.val f → f ∈ F)
    {u z : V} (hu : u ∈ v.val.val) (huz : G.Adj u z)
    (hmiss : z ∉ rootLabels G ((privateFinset ((conflictGraph G).induce F) M v).image Subtype.val) u) :
    (edgeIncidences G ((privateFinset ((conflictGraph G).induce F) M v).image Subtype.val) z).card = 0 := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  let f : G.edgeSet := ⟨s(u, z), huz⟩
  have hfv : f ≠ v.val := by
    intro h
    apply hmiss
    exact mem_filter.mpr ⟨(G.mem_neighborFinset u z).mpr huz, f,
      mem_image.mpr ⟨v, (mem_privateFinset H M v v).mpr (private_centre H M v hM hv), h.symm⟩, rfl⟩
  have hfvC := strongConflict_of_shared_endpoint G hfv (Sym2.mem_mk_left u z) hu
  have hfF : f ∈ F := hclosed f (strongConflict_symm G hfvC)
  let a : F := ⟨f, hfF⟩
  have haP : ¬ IsPrivate H M v a := by
    intro h
    apply hmiss
    exact mem_filter.mpr ⟨(G.mem_neighborFinset u z).mpr huz, f,
      mem_image.mpr ⟨a, (mem_privateFinset H M v a).mpr h, rfl⟩, rfl⟩
  have hex : ∃ w ∈ M, w ≠ v ∧ (a = w ∨ H.Adj a w) := by
    by_contra hn
    apply haP
    refine ⟨Or.inr hfvC, ?_⟩
    intro w hw hwv
    exact ⟨fun h => hn ⟨w, hw, hwv, Or.inl h⟩, fun h => hn ⟨w, hw, hwv, Or.inr h⟩⟩
  obtain ⟨w, hw, hwv, haw⟩ := hex
  have hwv' : w.val ≠ v.val := fun h => hwv (Subtype.ext h)
  have hnwv : ¬ StrongConflict G w.val v.val := hM.isIndepSet hw hv hwv
  have hawC : StrongConflict G w.val f := by
    rcases haw with haw | haw
    · have heq : w.val = f := (congrArg Subtype.val haw).symm
      exact (hnwv (strongConflict_of_shared_endpoint G hwv'
        (heq.symm ▸ Sym2.mem_mk_left u z) hu)).elim
    · exact strongConflict_symm G haw
  obtain ⟨p, q, hwq⟩ := Sym2.exists.mp (show ∃ s : Sym2 V, s = w.val.val from ⟨w.val.val, rfl⟩)
  obtain ⟨t, ht, htf⟩ := strongConflict_meets_cover G hwq.symm hawC
  have hzC : z ∈ endpointNeighbourCover G p q := by
    change t ∈ s(u, z) at htf
    rcases Sym2.mem_iff.mp htf with htu | htz
    · exact (hnwv (strongConflict_of_meets_cover G hwq.symm hwv' (htu ▸ ht) hu)).elim
    · exact htz ▸ ht
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro g hg
  obtain ⟨hgQ, hzg⟩ := mem_filter.mp hg
  obtain ⟨b, hb, hbg⟩ := mem_image.mp hgQ
  have hbp := (mem_privateFinset H M v b).mp hb
  have hbw := hbp.2 w hw hwv
  have hwb : w.val ≠ b.val := fun h => hbw.1 (Subtype.ext h.symm)
  have hzg' : z ∈ b.val.val := by
    change b.val = g at hbg
    rw [hbg]
    exact hzg
  exact hbw.2 (strongConflict_symm G
    (strongConflict_of_meets_cover G hwq.symm hwb hzC hzg'))

/-- A selected-subcubic private clique at a closed high-degree centre has at most thirteen edges. -/
theorem private_subcubic_card_le_thirteen
    (hΔ : ∀ x, G.degree x ≤ 4) (M : Finset F)
    (hM : ((conflictGraph G).induce F).IsMaximumIndepSet M)
    {v : F} (hv : v ∈ M)
    (hclosed : ∀ f, (conflictGraph G).Adj v.val f → f ∈ F)
    (h21 : 21 ≤ (conflictGraph G).degree v.val)
    (hd : ∀ x, (edgeIncidences G
      ((privateFinset ((conflictGraph G).induce F) M v).image Subtype.val) x).card ≤ 3) :
    (privateFinset ((conflictGraph G).induce F) M v).card ≤ 13 := by
  classical
  let H := (conflictGraph G).induce F
  let P := privateFinset H M v
  let Q := P.image Subtype.val
  change ∀ x, (edgeIncidences G Q x).card ≤ 3 at hd
  have hvQ : v.val ∈ Q := mem_image.mpr ⟨v,
    (mem_privateFinset H M v v).mpr (private_centre H M v hM hv), rfl⟩
  have hP : H.IsClique (P : Set F) := by
    intro a ha b hb hab
    exact private_isClique H M v hM hv ((mem_privateFinset H M v a).mp ha)
      ((mem_privateFinset H M v b).mp hb) hab
  have hQ := induced_clique_image (conflictGraph G) F P hP
  obtain ⟨u, w, hvw⟩ := Sym2.exists.mp (show ∃ s : Sym2 V, s = v.val.val from ⟨v.val.val, rfl⟩)
  have hdeg := high21_endpoints_degree_four G hΔ v.val hvw.symm h21
  have missing : ∀ x, G.degree x = 4 → ∃ y, G.Adj x y ∧ y ∉ rootLabels G Q x := by
    intro x hx
    have hn : ¬ G.neighborFinset x ⊆ rootLabels G Q x := by
      intro hs
      have hc := card_le_card hs
      have hb := hd x
      rw [SimpleGraph.card_neighborFinset_eq_degree, hx, rootLabels_card] at hc
      omega
    obtain ⟨y, hy, hyn⟩ := not_subset.mp hn
    exact ⟨y, (G.mem_neighborFinset x y).mp hy, hyn⟩
  obtain ⟨z, huz, hz⟩ := missing u hdeg.1
  obtain ⟨t, hwt, ht⟩ := missing w hdeg.2
  have hu : u ∈ v.val.val := hvw ▸ Sym2.mem_mk_left u w
  have hw : w ∈ v.val.val := hvw ▸ Sym2.mem_mk_right u w
  have hz0 := private_missing_edge_zero_incidence G F M hM hv hclosed hu huz hz
  have ht0 := private_missing_edge_zero_incidence G F M hM hv hclosed hw hwt ht
  have hzw : z ≠ w := fun h => hz (h ▸ mem_filter.mpr
    ⟨(G.mem_neighborFinset u w).mpr (G.mem_edgeSet.mp (hvw ▸ v.val.property)), v.val, hvQ, hvw.symm⟩)
  have htu : t ≠ u := fun h => ht (h ▸ mem_filter.mpr
    ⟨(G.mem_neighborFinset w u).mpr (G.mem_edgeSet.mp (hvw ▸ v.val.property)).symm,
      v.val, hvQ, hvw.symm.trans Sym2.eq_swap⟩)
  let C := endpointNeighbourCover G u w
  have hzC : z ∈ C := mem_union_left _ (mem_erase.mpr ⟨hzw, (G.mem_neighborFinset u z).mpr huz⟩)
  have htC : t ∈ C := mem_union_right _ (mem_erase.mpr ⟨htu, (G.mem_neighborFinset w t).mpr hwt⟩)
  have hzt : z ≠ t := fun h => high21_no_triangle_on_edge G hΔ v.val hvw.symm h21 huz (h.symm ▸ hwt)
  have htC' : t ∈ C.erase z := mem_erase.mpr ⟨hzt.symm, htC⟩
  have hc := high21_cover_card_eq_six G hΔ v.val hvw.symm h21
  have hez := card_erase_add_one hzC
  have het := card_erase_add_one htC'
  have hsz := sum_erase_add C (fun x => (edgeIncidences G Q x).card) hzC
  have hst := sum_erase_add (C.erase z) (fun x => (edgeIncidences G Q x).card) htC'
  have hb := sum_le_sum (s := (C.erase z).erase t) (fun x _ => hd x)
  simp only [sum_const, smul_eq_mul] at hb
  have hcount := clique_card_le_one_add_incidence_sum G Q hQ v.val hvQ hvw.symm
  have hQc : Q.card = P.card := card_image_of_injective P Subtype.val_injective
  change C.card = 6 at hc
  change (edgeIncidences G Q z).card = 0 at hz0
  change (edgeIncidences G Q t).card = 0 at ht0
  change Q.card ≤ 1 + ∑ x ∈ C, (edgeIncidences G Q x).card at hcount
  change P.card ≤ 13
  omega

end StrongEdge19
