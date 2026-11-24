/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.RecordEnumeration
public import GridHardness.SatDrawingSelectionCode
public import GridHardness.SatVertexCatalogueCode
public import GridHardness.SatBipartiteRecordsCode

/-!
# SAT Directed Records Code

The complete directed drawing is generated from SAT syntax with certified
cost. Exact-order lifts of its record lists connect the executable frontend
to the geometric backend, preserving the enumeration order.
-/

@[expose] public section

namespace GridHardness.SatDirectedRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open PlanarSatAssembly SatCompleteDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable abbrev label := SatDrawingSelectionCode.label

def code : Code SatTy DirectedBipartiteRecordsCode.InputTy :=
  .pair SatVertexCatalogueCode.code SatDrawingSelectionCode.records

theorem vertex_record_injective (x : SatTy.denote) :
    Function.Injective (SatBipartiteRecordsCode.vertexRecord x (label x)) := by
  intro u v h
  exact SatDrawingSelectionCode.label_injective x (congrArg Prod.fst h)

theorem vertex_records (x : SatTy.denote) (r : DirectedBipartiteRecordsCode.VertexTy.denote) :
    r∈SatVertexCatalogueCode.code.eval x ↔
      ∃v : Vertex x,r=SatBipartiteRecordsCode.vertexRecord x (label x) v :=
  SatVertexCatalogueCode.mem_code x r

theorem arc_record_injective (x : SatTy.denote) :
    Function.Injective (SatDirectedRouteLookupCode.record x (label x)) := by
  intro a b h
  exact SatDirectedRouteLookupCode.key_injective x (label x)
    (SatDrawingSelectionCode.label_injective x) (congrArg Prod.fst h)

theorem arc_record_selected (x : SatTy.denote) (a : Arc x) :
    SatDirectedRouteLookupCode.record x (label x) a=
      ((label x (source x a),label x (target x a)),
        SatDrawingSelectionCode.lookup.eval (x,(label x (source x a),label x (target x a)))) := by
  change (_, (route x a).map encodePoint)=_
  rw [SatCompleteDrawing.route_encoded]
  rfl

theorem arc_records (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈SatDrawingSelectionCode.records.eval x ↔
      ∃a : Arc x,r=SatDirectedRouteLookupCode.record x (label x) a := by
  rw [SatDrawingSelectionCode.mem_records]
  constructor
  · rintro ⟨u,v,ha,he⟩
    refine ⟨⟨(u,v),ha⟩,?_⟩
    rw [arc_record_selected]
    exact he
  · rintro ⟨a,rfl⟩
    exact ⟨source x a,target x a,a.property,arc_record_selected x a⟩

/-- The supplied syntax-driven lists preserve the exact record order expected
by the geometric compiler, including any repeated records. -/
theorem exact_input (x : SatTy.denote) :
    ∃ (vs : List (Vertex x)) (arcs : List (Arc x)),
      (∀v,v∈vs) ∧ (∀a,a∈arcs) ∧
        code.eval x=SatBipartiteRecordsCode.input x (label x) vs arcs := by
  obtain ⟨vs,hvs,hv⟩ := RecordEnumeration.exists_lift
    (SatVertexCatalogueCode.code.eval x) (SatBipartiteRecordsCode.vertexRecord x (label x))
    (vertex_record_injective x) (vertex_records x)
  obtain ⟨arcs,has,ha⟩ := RecordEnumeration.exists_lift
    (SatDrawingSelectionCode.records.eval x) (SatDirectedRouteLookupCode.record x (label x))
    (arc_record_injective x) (arc_records x)
  refine ⟨vs,arcs,hv,ha,?_⟩
  change (SatVertexCatalogueCode.code.eval x,SatDrawingSelectionCode.records.eval x)=
    (vs.map (SatBipartiteRecordsCode.vertexRecord x (label x)),
      arcs.map (SatDirectedRouteLookupCode.record x (label x)))
  rw [hvs,has]

theorem points (x : SatTy.denote) (hw : ∀ c∈x, c.length =3) :
    GridPointCode.points (SatBipartiteRecordsCode.code.eval (code.eval x))=
      (SatCompleteLayout.layout x hw).points := by
  obtain ⟨vs,arcs,hv,ha,he⟩ := exact_input x
  rw [he]
  exact SatBipartiteRecordsCode.points x (label x) hw
    (SatDrawingSelectionCode.label_injective x) arcs ha vs hv

/-- The complete SAT-to-rectangle program, before the final syntax guard. -/
def rectangles : Code SatTy GridPointCode.InputTy := .comp code SatBipartiteRecordsCode.code

theorem rectangles_points (x : SatTy.denote) (hw : ∀ c∈x, c.length =3) :
    GridPointCode.points (rectangles.eval x)=(SatCompleteLayout.layout x hw).points := points x hw

end GridHardness.SatDirectedRecordsCode
