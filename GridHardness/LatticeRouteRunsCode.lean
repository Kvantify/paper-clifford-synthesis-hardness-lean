/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteDirectionsCode
public import GridHardness.LatticeRouteRunCompressionCode

/-!
# Lattice Route Runs Code

The complete polynomial-cost lattice-route compressor. Its output is the
exact encoding of the existing semantic maximal straight runs on every input;
no unit-step, simplicity, or canonical-coordinate promise is needed to execute
or identify the result.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRunsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Signed point list to `(cardinal direction, positive step count)` records. -/
def routeCode : Code CycleInputTy RunsTy :=
  .comp LatticeRouteDirectionsCode.directionsCode compressCode

/-- The compiled program agrees exactly with the semantic
compressor, even for redundant signed-coordinate encodings. -/
theorem routeCode_eval (xs : CycleInputTy.denote) :
    routeCode.eval xs=(LatticeRouteRuns.compress (xs.map decoded)).map encodeRun := by
  change compressCode.eval (LatticeRouteDirectionsCode.directionsCode.eval xs)=_
  rw [LatticeRouteDirectionsCode.directionsCode_eval,compressCode_encode]
  rfl

theorem routeCode_encoded (xs : List (Int ×Int)) :
    routeCode.eval (xs.map encodePoint)=(LatticeRouteRuns.compress xs).map encodeRun := by
  rw [routeCode_eval,List.map_map]
  simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
  exact congrArg (fun l => (LatticeRouteRuns.compress l).map encodeRun) (List.map_id xs)

/-- The output count charges only actual input edges. -/
theorem routeCode_step_count (xs : CycleInputTy.denote) :
    ((routeCode.eval xs).map Prod.snd).sum=xs.length-1 := by
  rw [routeCode_eval,List.map_map]
  change ((LatticeRouteRuns.compress (xs.map decoded)).map Prod.snd).sum=_
  rw [LatticeRouteRuns.run_step_count,List.length_map]

theorem routeCode_count (xs : CycleInputTy.denote) :
    (routeCode.eval xs).length≤xs.length-1 := by
  rw [routeCode_eval,List.length_map]
  simpa only [List.length_map] using LatticeRouteRuns.run_count_le (xs.map decoded)

theorem routeCode_run_bounds (xs : CycleInputTy.denote) (r : RunTy.denote)
    (hr : r ∈routeCode.eval xs) : r.1<4 ∧ 0<r.2 ∧ r.2≤xs.length-1 := by
  have hm : r.2∈(routeCode.eval xs).map Prod.snd := List.mem_map_of_mem hr
  have hsum : r.2≤((routeCode.eval xs).map Prod.snd).sum := List.le_sum_of_mem hm
  rw [routeCode_step_count] at hsum
  rw [routeCode_eval] at hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  exact ⟨q.1.isLt,LatticeRouteRuns.runs_positive _ q hq,hsum⟩

/-- The input route itself is a sufficient unary padding reservoir for every
run length; the compiler need not iterate over a binary numeral. -/
theorem routeCode_run_le_length (xs : CycleInputTy.denote) (r : RunTy.denote)
    (hr : r ∈routeCode.eval xs) : r.2≤xs.length := by
  exact ((routeCode_run_bounds xs r hr).2.2).trans (Nat.sub_le _ _)

end GridHardness.LatticeRouteRunsCode
