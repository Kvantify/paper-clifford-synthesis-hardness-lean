/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatResidualDrawing
public import GridHardness.CorrectedSatIntervalResidualRun

/-!
# SAT Residual Arcs

Every residual candidate route is an actual arc of the final graph.
Empty columns and both extreme tails use the exact endpoint identities
preserved by the complete interval sweep, for every occurrence permutation.
-/

public section

namespace GridHardness.SatResidualDrawing
open PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false

theorem unsplit_edge_is_arc {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (i : Fin (3 *m))
    (hi : SatCrossingRetirement.Segments.EmptyColumn p i) (r : Fin 4) :
    (PermutationGraph.graph φ p).adj
      (source φ p ⟨i,r,.unsplit hi⟩) (target φ p ⟨i,r,.unsplit hi⟩) :=
  ResidualEdges.permutation_unsplit φ p i hi r

theorem edge_is_arc {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) := by
  rcases e with ⟨i,r,part⟩
  cases part with
  | unsplit h => exact unsplit_edge_is_arc φ p i h r
  | above j hj =>
    have h := ResidualEdges.permutation_above φ p i j hj r
    by_cases hr : r.val%2=0 <;>
      simpa only [source,target,sourceWire,targetWire,hr,ite_true,ite_false,
        input,output,PermutationWirePlacement.vertex_fresh] using h
  | below j hj =>
    have h := ResidualEdges.permutation_below φ p i j hj r
    by_cases hr : r.val%2=0 <;>
      simpa only [source,target,sourceWire,targetWire,hr,ite_true,ite_false,
        input,output,PermutationWirePlacement.vertex_fresh] using h

end GridHardness.SatResidualDrawing
