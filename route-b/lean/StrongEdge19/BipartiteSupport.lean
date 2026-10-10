module

public import StrongEdge19.OuterSupport

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem edges_crossing_parts_card_le_product
    (Q : Finset G.edgeSet) (L R : Finset V)
    (hcross : ∀ e ∈ Q, ∃ u ∈ L, ∃ v ∈ R, e.val = s(u, v)) :
    Q.card ≤ L.card * R.card := by
  rw [← card_product]
  apply card_le_via_relation Q (L ×ˢ R) (fun e p => e.val = s(p.1, p.2))
  · intro e he
    obtain ⟨u, hu, v, hv, hev⟩ := hcross e he
    exact ⟨(u, v), mem_product.mpr ⟨hu, hv⟩, hev⟩
  · intro e _ f _ p hep hfp
    exact Subtype.ext (hep.trans hfp.symm)

theorem small_complementary_types_outer_card_le_two
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (D : Finset V) (hDc : D.card ≤ 3)
    (hD : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ D)
    (ht : ∀ x ∈ D, (rootType G r x).card ≤ 2) :
    (outerEdges G Q r).card ≤ 2 := by
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootLabels G Q r).card by omega)
  let L := D.filter (fun x => a ∈ rootType G r x)
  let R := D.filter (fun x => a ∉ rootType G r x)
  have hsum : L.card + R.card ≤ 3 := by
    have he := card_filter_add_card_filter_not (s := D) (p := fun x => a ∈ rootType G r x)
    change L.card + R.card = D.card at he
    omega
  have hcross : ∀ e ∈ outerEdges G Q r, ∃ u ∈ L, ∃ v ∈ R, e.val = s(u, v) := by
    intro e heo
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hu := hD e heo u (hev ▸ Sym2.mem_mk_left u v)
    have hv := hD e heo v (hev ▸ Sym2.mem_mk_right u v)
    have htu := ht u hu
    have htv := ht v hv
    have hcov := outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo
    have hc := card_le_card hcov
    have hi := card_union_add_card_inter (rootType G r u) (rootType G r v)
    have hdis : Disjoint (rootType G r u) (rootType G r v) := by
      apply disjoint_iff_inter_eq_empty.mpr
      apply card_eq_zero.mp
      omega
    rcases mem_union.mp (hcov ha) with hau | hav
    · exact ⟨u, mem_filter.mpr ⟨hu, hau⟩, v,
        mem_filter.mpr ⟨hv, fun h => disjoint_left.mp hdis hau h⟩, hev.symm⟩
    · exact ⟨v, mem_filter.mpr ⟨hv, hav⟩, u,
        mem_filter.mpr ⟨hu, fun h => disjoint_left.mp hdis h hav⟩, hev.symm.trans Sym2.eq_swap⟩
  have hc := edges_crossing_parts_card_le_product G (outerEdges G Q r) L R hcross
  have hl : L.card ≤ 3 := by omega
  have hcases : L.card = 0 ∨ L.card = 1 ∨ L.card = 2 ∨ L.card = 3 := by omega
  rcases hcases with h | h | h | h <;> rw [h] at hc <;> omega

end StrongEdge19
