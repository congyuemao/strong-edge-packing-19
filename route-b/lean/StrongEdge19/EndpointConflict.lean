module

public import StrongEdge.Bounds.ConflictDegree

@[expose] public section

namespace StrongEdge19

open Finset StrongEdge

variable {V : Type*} (G : SimpleGraph V)

theorem strongConflict_of_shared_endpoint {e f : G.edgeSet} (hne : e ≠ f)
    {u : V} (hue : u ∈ e.val) (huf : u ∈ f.val) : StrongConflict G e f :=
  ⟨hne, Or.inl (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, u, hue, huf⟩)⟩

/-- The connecting edge is an arbitrary original edge, with no selection hypothesis. -/
theorem strongConflict_of_adjacent_endpoints {e f : G.edgeSet} (hne : e ≠ f)
    {u v : V} (hue : u ∈ e.val) (hvf : v ∈ f.val) (huv : G.Adj u v) :
    StrongConflict G e f := by
  let g : G.edgeSet := ⟨s(u, v), huv⟩
  by_cases heg : e = g
  · exact strongConflict_of_shared_endpoint G hne (heg.symm ▸ Sym2.mem_mk_right u v) hvf
  by_cases hgf : g = f
  · exact strongConflict_of_shared_endpoint G hne hue (hgf ▸ Sym2.mem_mk_left u v)
  exact ⟨hne, Or.inr ⟨g,
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨heg, u, hue, Sym2.mem_mk_left u v⟩,
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hgf, v, Sym2.mem_mk_right u v, hvf⟩⟩⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem strongConflict_of_meets_cover {u v : V} {e f : G.edgeSet}
    (he : e.val = s(u, v)) (hne : e ≠ f)
    {w : V} (hw : w ∈ endpointNeighbourCover G u v) (hwf : w ∈ f.val) :
    StrongConflict G e f := by
  rcases mem_union.mp hw with hw | hw
  · exact strongConflict_of_adjacent_endpoints G hne (he.symm ▸ Sym2.mem_mk_left u v) hwf
      ((G.mem_neighborFinset u w).mp (mem_erase.mp hw).2)
  · exact strongConflict_of_adjacent_endpoints G hne (he.symm ▸ Sym2.mem_mk_right u v) hwf
      ((G.mem_neighborFinset v w).mp (mem_erase.mp hw).2)

end StrongEdge19
