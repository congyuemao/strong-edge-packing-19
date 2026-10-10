module

import all StrongEdge19.BipartiteSupport
import all StrongEdge19.ClosedCore
import all StrongEdge19.Compensation
import all StrongEdge19.CriticalHighDegree
import all StrongEdge19.CriticalNineteen
import all StrongEdge19.CriticalNormalization
import all StrongEdge19.EndpointConflict
import all StrongEdge19.High20Root
import all StrongEdge19.High20Triple
import all StrongEdge19.High22Root
import all StrongEdge19.High23Root
import all StrongEdge19.Main
import all StrongEdge19.NineteenRigidity
import all StrongEdge19.OuterSaturation
import all StrongEdge19.OuterSupport
import all StrongEdge19.Packing
import all StrongEdge19.PositiveDeficits
import all StrongEdge19.PrivateSubcubic
import all StrongEdge19.QuadCore
import all StrongEdge19.QuadLoad
import all StrongEdge19.QuadType
import all StrongEdge19.Root19
import all StrongEdge19.RootLoad
import all StrongEdge19.RootSaturation
import all StrongEdge19.SmallTypes
import all StrongEdge19.Tertiary
import all StrongEdge19.TypeCover
import Lean.Util.FoldConsts

open Lean Elab Command

-- Read the elaborated type and proof dependencies, restricted to the extension namespace.
-- This diagnostic declares no mathematical constants and is not imported by the proof.
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``StrongEdge19.zero_deficit_degree_le_twenty,
      ``StrongEdge19.critical_degree_nineteen_forces_selected_twenty,
      ``StrongEdge19.zero_deficit_impossible, ``StrongEdge19.prescribed_edge_bound19] do
    unless (env.find? root).any (fun info => (info.value? (allowOpaque := true)).isSome) do
      throwError m!"Proof body unavailable for {root}"
    let mut pending := #[root]
    let mut seen : NameSet := {}
    let mut direct : Array String := #[]
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet do
          if dep.toString.startsWith "StrongEdge19." then
            if name == root then direct := direct.push dep.toString
            if !seen.contains dep then pending := pending.push dep
    let dependencies := (seen.toArray.filter (· != root)).map Name.toString
    liftIO <| IO.println <| Json.compress <| Json.mkObj [
      ("declaration", toJson root.toString),
      ("direct_extension_dependencies", toJson (direct.qsort (· < ·))),
      ("transitive_extension_dependencies", toJson (dependencies.qsort (· < ·)))]
