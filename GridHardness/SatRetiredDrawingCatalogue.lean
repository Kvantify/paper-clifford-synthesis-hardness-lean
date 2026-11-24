/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetiredDrawingCode

/-!
# SAT Retired Drawing Catalogue

The retirement compiler enumerates the existing final drawing catalogue,
with the same endpoint labels and point lists.
-/

@[expose] public section

namespace GridHardness.SatRetiredDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open PlanarSatAssembly CorrectedSatInterval SatRetirementGeometryCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxHeartbeats 800000

def catalogueIndex (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    SatWireDrawingGeometry.Edge x := .inl (.inl (.inl (.inr (j,e))))

theorem vertexRecord_actual (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) :
    vertexRecord x j v=
      (SatClauseBodyCode.actualLabel x (SatRetiredSideDrawing.vertex (finiteFormula x) (perm x) (j,v)),
        encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x)
          (SatRetiredSideDrawing.vertex (finiteFormula x) (perm x) (j,v)))) := by
  rw [SatRetiredSideDrawing.actualPoint_vertex]; rfl

theorem routeRecord_actual (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    routeRecord x j e=
      ((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x j e)),
        SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x j e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x j e)).map encodePoint) := rfl

theorem emitted_arc (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatWireDrawingGeometry.source x (catalogueIndex x j e))
      (SatWireDrawingGeometry.target x (catalogueIndex x j e)) :=
  SatWireDrawingGeometry.edge_is_arc x _

theorem label_injective (x : SatTy.denote) :
    Function.Injective (fun jv : Fin (3*x.length)×Fin 8 => label x jv.1 jv.2) := by
  intro a b h
  have he := (PermutationGraph.number _ _).injective (Fin.ext h)
  exact Sum.inl.inj (PermutationWirePlacement.vertex_injective _ _ he)

theorem key_injective (x : SatTy.denote) :
    Function.Injective (fun je : Fin (3*x.length)×Fin 6 => (routeRecord x je.1 je.2).1) := by
  rintro ⟨j,e⟩ ⟨k,f⟩ h
  have hs := @label_injective x (j,(SatRetiredSideDrawing.localEndpoints e).1)
    (k,(SatRetiredSideDrawing.localEndpoints f).1) (congrArg Prod.fst h)
  have ht := @label_injective x (j,(SatRetiredSideDrawing.localEndpoints e).2)
    (k,(SatRetiredSideDrawing.localEndpoints f).2) (congrArg Prod.snd h)
  have hj : j=k := congrArg (fun z : Fin (3*x.length)×Fin 8 => z.1) hs
  have hef : e=f := SatRetiredSideDrawing.localEndpoints_injective
    (Prod.ext (congrArg (fun z : Fin (3*x.length)×Fin 8 => z.2) hs)
      (congrArg (fun z : Fin (3*x.length)×Fin 8 => z.2) ht))
  exact Prod.ext hj hef

theorem functional (x : SatTy.denote) : DirectedRouteLookupCode.Functional (routes.eval x) := by
  intro r hr s hs he
  obtain ⟨j,e,rfl⟩ := (mem_routes x r).mp hr
  obtain ⟨k,f,rfl⟩ := (mem_routes x s).mp hs
  have h := @key_injective x (j,e) (k,f) he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
  rfl

def lookup : Code (.pair SatTy DirectedRouteLookupCode.KeyTy) CycleInputTy :=
  .comp (.pair (.comp .fst routes) .snd) DirectedRouteLookupCode.code

theorem lookup_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    lookup.eval (x,(routeRecord x j e).1)=
      (SatRetiredSideDrawing.route (perm x) (j,e)).map encodePoint := by
  change DirectedRouteLookupCode.code.eval (routes.eval x,(routeRecord x j e).1)=_
  apply DirectedRouteLookupCode.code_eq_of_mem
  · exact (mem_routes x _).mpr ⟨j,e,rfl⟩
  · exact functional x

end GridHardness.SatRetiredDrawingCode
