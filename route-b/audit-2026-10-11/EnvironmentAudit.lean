module

import all StrongEdge.Basic
import all StrongEdge.Conflict
import all StrongEdge.PrivateExchange
import all StrongEdge.DoubleCount
import all StrongEdge.Packing
import all StrongEdge.Tests
import all StrongEdge.Bounds.ConflictDegree
import all StrongEdge.Bounds.ConflictRigidity
import all StrongEdge.MinimalPacking
import all StrongEdge.Bounds.High24
import all StrongEdge.High24Packing
import all StrongEdge.Bounds.EdgeCounting
import all StrongEdge.Bounds.High23Local
import all StrongEdge.Bounds.High23Support
import all StrongEdge.Bounds.High23Outer
import all StrongEdge.Bounds.High23Four
import all StrongEdge.Bounds.High23
import all StrongEdge.High23Packing
import all StrongEdge.Bounds.High22Local
import all StrongEdge.Bounds.RootCounting
import all StrongEdge.Bounds.High22Support
import all StrongEdge.Bounds.High22RootFour
import all StrongEdge.Bounds.High22Heavy
import all StrongEdge.Bounds.High22Subcubic
import all StrongEdge.Bounds.High22
import all StrongEdge.High22Packing
import all StrongEdge.Bounds.SubcubicEighteen
import all StrongEdge.Bounds.DegreeTwoClique
import all StrongEdge.Bounds.High21Local
import all StrongEdge.Bounds.High21Support
import all StrongEdge.Bounds.High21Double
import all StrongEdge.Bounds.High21LargeType
import all StrongEdge.Bounds.High21RootFour
import all StrongEdge.Bounds.High21
import all StrongEdge.High21Packing
import all StrongEdge.Bounds.High20Local
import all StrongEdge.Bounds.High20Four
import all StrongEdge.Bounds.High20TwoTriples
import all StrongEdge.Bounds.High20Slots
import all StrongEdge.Bounds.High20Outer
import all StrongEdge.Bounds.High20UniqueTriple
import all StrongEdge.Bounds.High20
import all StrongEdge.High20Packing
import all StrongEdge.MinimalPacking195
import all StrongEdge.Bounds.High20Improved
import all StrongEdge.Bounds.High23Improved
import all StrongEdge.Packing195
import all StrongEdge.Tests195
import all StrongEdge.Bounds.High21ImprovedRoot
import all StrongEdge.Bounds.High22ImprovedRoot
import all StrongEdge.Bounds.SubcubicBoundary
import all StrongEdge.Bounds.SubcubicSeventeen
import all StrongEdge.Bounds.High21Improved
import all StrongEdge.Packing195Continuation
import all StrongEdge.Bounds.SubcubicDefect
import all StrongEdge.Bounds.High22SupportSize
import all StrongEdge.Bounds.LowSupportGeometry
import all StrongEdge.Bounds.High22Improved
import all StrongEdge.Packing195Thresholds
import all StrongEdge.Bounds.TwentyCliqueRoot
import all StrongEdge.Bounds.TwentyCliqueCounting
import all StrongEdge.Bounds.TwentyCliqueTypes
import all StrongEdge.Bounds.TwentyCliqueSaturation
import all StrongEdge.Bounds.TwentyCliqueComponent
import all StrongEdge.Bounds.TwentyCliqueParts
import all StrongEdge.Bounds.TwentyCliqueRigidity
import all StrongEdge.Packing195Unconditional
import all StrongEdge.TightComponents
import all StrongEdge.Tests195Unconditional
import all StrongEdge
import all StrongEdge19.Root19
import all StrongEdge19.RootLoad
import all StrongEdge19.RootSaturation
import all StrongEdge19.OuterSupport
import all StrongEdge19.TypeCover
import all StrongEdge19.OuterSaturation
import all StrongEdge19.High20Triple
import all StrongEdge19.SmallTypes
import all StrongEdge19.High20Root
import all StrongEdge19.Tertiary
import all StrongEdge19.Compensation
import all StrongEdge19.CriticalNormalization
import all StrongEdge19.EndpointConflict
import all StrongEdge19.PrivateSubcubic
import all StrongEdge19.High22Root
import all StrongEdge19.High23Root
import all StrongEdge19.CriticalHighDegree
import all StrongEdge19.QuadType
import all StrongEdge19.QuadLoad
import all StrongEdge19.BipartiteSupport
import all StrongEdge19.QuadCore
import all StrongEdge19.ClosedCore
import all StrongEdge19.NineteenRigidity
import all StrongEdge19.CriticalNineteen
import all StrongEdge19.PositiveDeficits
import all StrongEdge19.Packing
import all StrongEdge19.Main
import all StrongEdge19
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let names := env.constants.fold (fun acc n _ =>
    let origin := (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
    if origin.any (fun m => m.toString.startsWith "StrongEdge." ||
        m.toString.startsWith "StrongEdge19." || m == `StrongEdge || m == `StrongEdge19)
    then acc.push n else acc) (#[] : Array Name)
  for n in names.qsort Name.lt do
    let some info := env.find? n | throwError m!"Missing declaration {n}"
    let axioms ← collectAxioms n
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError m!"Unexpected axiom {ax} in {n}"
    if info.isUnsafe || info.isAxiom then
      throwError m!"Unsafe declaration or project axiom {n}"
    if info.isTheorem && (info.value? (allowOpaque := true)).isNone then
      throwError m!"Theorem body unavailable for dependency inspection: {n}"
    liftIO <| IO.println <| Json.compress <| Json.mkObj [
      ("name", toJson n.toString),
      ("origin_module", toJson ((env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?).get!.toString),
      ("is_theorem", toJson info.isTheorem),
      ("has_body", toJson (info.value? (allowOpaque := true)).isSome),
      ("unsafe", toJson info.isUnsafe),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependencies", toJson ((info.getUsedConstantsAsSet.toArray.map Name.toString).qsort (· < ·)))]

#check @StrongEdge19.prescribed_edge_bound19
#check @StrongEdge19.induced_matching_packing19_with_connected_component_count
#check @StrongEdge19.zero_deficit_candidate_degree_eq_nineteen
#check @StrongEdge19.critical_degree_nineteen_forces_selected_twenty
#check @StrongEdge19.high19_nineteen_clique_extends_to_twenty

namespace IndependentAudit
open Finset StrongEdge StrongEdge19
open scoped Classical
-- No decidability, optimality, connectivity or clique assumptions in the interface.
theorem endpoint_matching_statement {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hDelta : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
        ∀ u ∈ e.val, ∀ v ∈ f.val, u ≠ v ∧ ¬ G.Adj u v) ∧
      F.card ≤ 19 * M.card + (tightComponentsIn G F).card := by
  classical
  obtain ⟨M, hMF, hM, hb⟩ := induced_matching_packing19_with_connected_component_count G hDelta F
  refine ⟨M, hMF, ?_, hb⟩
  intro e he f hf hef u hu v hv
  refine ⟨?_, ?_⟩
  · intro huv
    subst v
    exact hM he hf hef (strongConflict_of_shared_endpoint G hef hu hv)
  · intro huv
    exact hM he hf hef (strongConflict_of_adjacent_endpoints G hef hu hv huv)

#check @endpoint_matching_statement
#print axioms endpoint_matching_statement
end IndependentAudit
