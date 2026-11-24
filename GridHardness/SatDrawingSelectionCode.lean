/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDrawingCatalogueCode
public import GridHardness.SatRouteCoverage
public import GridHardness.DirectedRouteSelectionCode

/-!
# SAT Drawing Selection Code

Executable route selection from the complete SAT-fed catalogue. Selection
returns the first matching endpoint record. Its geometric witness belongs to
the proved simultaneous catalogue, even if several indices share a key.
-/

@[expose] public section

namespace GridHardness.SatDrawingSelectionCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] SatDrawingCatalogueCode.code DirectedRouteLookupCode.code
  DirectedRouteSelectionCode.code

abbrev Vertex := SatRouteCatalogue.Vertex
noncomputable abbrev label := SatClauseBodyCode.actualLabel

theorem label_injective (x : SatTy.denote) : Function.Injective (label x) := by
  intro u v h
  exact (CorrectedSatInterval.PermutationGraph.number (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x))).injective (Fin.ext h)

def lookup : Code (.pair SatTy DirectedRouteLookupCode.KeyTy) CycleInputTy :=
  .comp (.pair (.comp .fst SatDrawingCatalogueCode.code) .snd) DirectedRouteLookupCode.code

def records : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  .comp SatDrawingCatalogueCode.code DirectedRouteSelectionCode.code

/-- A proof-only catalogue index realizes the computably selected point list.
The source, target, and entire route are fixed by the executable lookup. -/
theorem selected_exists (x : SatTy.denote) (u v : Vertex x)
    (ha : (SatClauseOrder.graph (finiteFormula x)).adj u v) :
    ∃ e : SatWireDrawingGeometry.Edge x,
      SatWireDrawingGeometry.source x e=u ∧ SatWireDrawingGeometry.target x e=v ∧
      (SatWireDrawingGeometry.route x e).map encodePoint=lookup.eval (x,(label x u,label x v)) := by
  obtain ⟨a,hs,ht⟩ := SatRouteCoverage.arc_covered x u v ha
  have hm : ∃ r∈SatDrawingCatalogueCode.code.eval x,r.1=(label x u,label x v) := by
    refine ⟨SatDrawingCatalogueCode.catalogueRecord x a,
      (SatDrawingCatalogueCode.mem_code x _).mpr ⟨a,rfl⟩,?_⟩
    change (label x (SatWireDrawingGeometry.source x a),label x (SatWireDrawingGeometry.target x a))=_
    rw [hs,ht]
  have hk := DirectedRouteSelectionCode.code_lookup_mem (SatDrawingCatalogueCode.code.eval x)
    (label x u,label x v) hm
  obtain ⟨e,he⟩ := (SatDrawingCatalogueCode.mem_code x _).mp hk
  refine ⟨e,?_,?_,?_⟩
  · exact @label_injective x (SatWireDrawingGeometry.source x e) u
      (congrArg (fun r : DirectedRouteLookupCode.RecordTy.denote => r.1.1) he).symm
  · exact @label_injective x (SatWireDrawingGeometry.target x e) v
      (congrArg (fun r : DirectedRouteLookupCode.RecordTy.denote => r.1.2) he).symm
  · exact (congrArg (fun r : DirectedRouteLookupCode.RecordTy.denote => r.2) he).symm

theorem mem_records (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈records.eval x ↔ ∃ u v : Vertex x,
      (SatClauseOrder.graph (finiteFormula x)).adj u v ∧
        r=((label x u,label x v),lookup.eval (x,(label x u,label x v))) := by
  change r∈DirectedRouteSelectionCode.code.eval (SatDrawingCatalogueCode.code.eval x) ↔ _
  rw [DirectedRouteSelectionCode.mem_code]
  constructor
  · rintro ⟨⟨s,hs,hk⟩,hp⟩
    obtain ⟨e,rfl⟩ := (SatDrawingCatalogueCode.mem_code x s).mp hs
    refine ⟨SatWireDrawingGeometry.source x e,SatWireDrawingGeometry.target x e,
      SatWireDrawingGeometry.edge_is_arc x e,?_⟩
    apply Prod.ext
    · exact hk.symm
    · change r.2=DirectedRouteLookupCode.code.eval (SatDrawingCatalogueCode.code.eval x,
        (label x (SatWireDrawingGeometry.source x e),label x (SatWireDrawingGeometry.target x e)))
      change (label x (SatWireDrawingGeometry.source x e),
        label x (SatWireDrawingGeometry.target x e))=r.1 at hk
      rw [hk]
      exact hp
  · rintro ⟨u,v,ha,rfl⟩
    obtain ⟨e,hs,ht,_⟩ := selected_exists x u v ha
    refine ⟨⟨SatDrawingCatalogueCode.catalogueRecord x e,
      (SatDrawingCatalogueCode.mem_code x _).mpr ⟨e,rfl⟩,?_⟩,rfl⟩
    change (label x (SatWireDrawingGeometry.source x e),label x (SatWireDrawingGeometry.target x e))=_
    rw [hs,ht]

theorem records_functional (x : SatTy.denote) : DirectedRouteLookupCode.Functional (records.eval x) := by
  change DirectedRouteLookupCode.Functional (DirectedRouteSelectionCode.code.eval _)
  rw [DirectedRouteSelectionCode.code_eval]
  exact DirectedRouteSelectionCode.functional _

end GridHardness.SatDrawingSelectionCode
