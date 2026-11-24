/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVerticalDrawing
public import GridHardness.CorrectedSatIntervalVerticalPermutation

/-!
# SAT Vertical Arcs

Every vertical connector joins actual arc endpoints of the completed
SAT sweep. The theorem handles both chronological orders of the crossings
and the alternating directions of the four lanes.
-/

public section

namespace GridHardness.SatVerticalDrawing
open PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false

theorem edge_is_arc {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) := by
  have h := VerticalEdges.permutation_vertical φ p e.1.val.1 e.1.val.2.1
    e.1.val.2.2 e.1.property e.2
  by_cases hr : e.2.val%2=0 <;>
    simpa only [source,target,endpoints,hr,ite_true,ite_false,lowerCell,upperCell,
      inputPort,outputPort,SatRetainedDrawing.vertex] using h

end GridHardness.SatVerticalDrawing
