/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedBipartitePlacementCode
public import GridHardness.SatBipartitePlacement

/-!
# SAT Bipartite Placement Code

The canonical local port selector and four-point placement program agree
exactly with the actual SAT bipartite replacement. The explicit directed
anchor and its incidence records are inputs here; its cost bound starts at these
records; `SatDirectedRecordsCode` generates them from SAT syntax.
-/

@[expose] public section

namespace GridHardness.SatBipartitePlacementCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open DirectedPortSelectionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

noncomputable def records (x : SatTy.denote) (v : SatCompleteDrawing.Vertex x) : PortsTy.denote :=
  (SatBipartitePorts.incidencePorts x v).map encodePort

noncomputable def input (x : SatTy.denote) (v : SatCompleteDrawing.Vertex x) :
    DirectedBipartitePlacementCode.InputTy.denote :=
  (encodePoint (SatCompleteDrawing.point x v),records x v)

theorem records_length (x : SatTy.denote) (v : SatCompleteDrawing.Vertex x) :
    (records x v).length≤3 := by
  simpa only [records, List.length_map] using SatBipartitePorts.incidencePorts_length_le x v

/-- The semantic port choice agrees with this executable finite selection. -/
theorem selector (x : SatTy.denote) (hw : ∀ c∈x, c.length =3) (v : SatCompleteDrawing.Vertex x) :
    DirectedPortSelectionCode.code.eval (records x v)=
      ((SatBipartitePorts.choose x hw v).incoming,(SatBipartitePorts.choose x hw v).direction.val) := by
  change DirectedPortSelectionCode.code.eval ((SatBipartitePorts.incidencePorts x v).map encodePort)=_
  rw [DirectedPortSelectionCode.code_eval, ← SatBipartitePorts.choose_eq_selector x hw v]
  rfl

/-- All four actual replacement coordinates, in internal-path order. -/
theorem points (x : SatTy.denote) (hw : ∀ c∈x, c.length =3) (v : SatCompleteDrawing.Vertex x) :
    DirectedBipartitePlacementCode.code.eval (input x v)=
      [encodePoint (SatBipartitePlacement.point x hw (v,0)),
       encodePoint (SatBipartitePlacement.point x hw (v,1)),
       encodePoint (SatBipartitePlacement.point x hw (v,2)),
       encodePoint (SatBipartitePlacement.point x hw (v,3))] := by
  have h := DirectedBipartitePlacementCode.code_eval
    (encodePoint (SatCompleteDrawing.point x v)) (SatBipartitePorts.incidencePorts x v)
  rw [← SatBipartitePorts.choose_eq_selector x hw v] at h
  simpa only [input, records, GridAssembly.Encoding.decode_encode,
    SatBipartitePlacement.point, DirectedScaledLayout.vertex] using h

/-- These are exactly the outgoing and incoming cuts used by the external
sixteen-fold subdivided routes. -/
theorem radii (x : SatTy.denote) (hw : ∀ c∈x, c.length =3) (v : SatCompleteDrawing.Vertex x) :
    DirectedBipartitePlacementCode.radii.eval (records x v)=
      (SatBipartitePlacement.portRadius x hw v false,SatBipartitePlacement.portRadius x hw v true) := by
  change DirectedBipartitePlacementCode.radii.eval
    ((SatBipartitePorts.incidencePorts x v).map encodePort)=_
  rw [DirectedBipartitePlacementCode.radii_eval, ← SatBipartitePorts.choose_eq_selector x hw v]
  rfl

/-- The finite selector works with any enumeration of precisely the actual
incidence set, independently of the order emitted by the SAT compiler. -/
theorem selector_of_records (x : SatTy.denote) (hw : ∀ c∈x, c.length =3)
    (v : SatCompleteDrawing.Vertex x) (rs : List DirectedPortSelection.Port)
    (hr : ∀ p, p∈rs ↔ p ∈SatBipartitePorts.incidencePorts x v) :
    DirectedPortSelectionCode.code.eval (rs.map encodePort)=
      ((SatBipartitePorts.choose x hw v).incoming,(SatBipartitePorts.choose x hw v).direction.val) := by
  rw [DirectedPortSelectionCode.code_eval,
    DirectedPortSelection.choose_congr rs (SatBipartitePorts.incidencePorts x v) hr,
    ← SatBipartitePorts.choose_eq_selector x hw v]
  rfl

end GridHardness.SatBipartitePlacementCode
