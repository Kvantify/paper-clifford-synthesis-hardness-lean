/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatWireDrawingDirections
public import GridHardness.SatVerticalArcs
public import GridHardness.SatResidualArcs

/-!
# SAT Wire Drawing Arcs

Soundness of the simultaneous route catalogue: every listed route is
an arc of the final graph. `SatRouteCoverage` proves the converse, that every
final graph arc occurs in the catalogue.
-/

public section

namespace GridHardness.SatWireDrawingGeometry
open CliffordComplexity PlanarSatAssembly
set_option autoImplicit false

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  rcases e with (e | e) | e
  · exact SatLastLinkAssembly.edge_is_arc x e
  · exact SatVerticalDrawing.edge_is_arc _ _ e
  · exact SatResidualDrawing.edge_is_arc _ _ e

end GridHardness.SatWireDrawingGeometry
