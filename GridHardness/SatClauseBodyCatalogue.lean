/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseBodyCode
public import GridHardness.SatRouteCatalogue

/-!
# SAT Clause Body Catalogue

The executable clause-body records use the existing final graph's
vertex numbers and actual geometric catalogue entries. This local family
contains every clause-body vertex and internal edge, with functional endpoint
keys. SatDrawingCatalogueCode incorporates this family into the complete
executable catalogue used for route selection.
-/

@[expose] public section

namespace GridHardness.SatClauseBodyCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxHeartbeats 800000

noncomputable def actualLabel (x : SatTy.denote)
    (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) : Nat :=
  (CorrectedSatInterval.PermutationGraph.number (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) v).val

theorem actualLabel_clause (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    actualLabel x (SatClauseOrder.vertex (finiteFormula x) c v)=label x c v :=
  SatClauseOrder.vertex_names (finiteFormula x) c v

theorem vertexRecord_actual (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    vertexRecord x c v=
      (actualLabel x (SatClauseOrder.vertex (finiteFormula x) c v),
        encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x)
          (SatClauseOrder.vertex (finiteFormula x) c v))) := by
  rw [actualLabel_clause,SatGlobalVertexPlacement.actualPoint_clause]
  rfl

/-- The explicit injection into the already proved global route catalogue. -/
def catalogueIndex (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    SatWireDrawingGeometry.Edge x :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.internal c e)))))))))

theorem catalogueIndex_source (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    SatWireDrawingGeometry.source x (catalogueIndex x c e)=
      SatClauseOrder.vertex (finiteFormula x) c (PlanarSatClause.Lattice.edge e).1 := rfl

theorem catalogueIndex_target (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    SatWireDrawingGeometry.target x (catalogueIndex x c e)=
      SatClauseOrder.vertex (finiteFormula x) c (PlanarSatClause.Lattice.edge e).2 := rfl

theorem catalogueIndex_route (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    SatWireDrawingGeometry.route x (catalogueIndex x c e)=SatClauseOrder.route c e := rfl

/-- The record matches the existing catalogue, including endpoint numbering. -/
theorem routeRecord_actual (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    routeRecord x c e=
      ((actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x c e)),
        actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x c e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x c e)).map encodePoint) := by
  rw [catalogueIndex_source,catalogueIndex_target,catalogueIndex_route,
    actualLabel_clause,actualLabel_clause]
  rfl

theorem emitted_arc (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatClauseOrder.vertex (finiteFormula x) c (PlanarSatClause.Lattice.edge e).1)
      (SatClauseOrder.vertex (finiteFormula x) c (PlanarSatClause.Lattice.edge e).2) :=
  SatClauseDrawing.edge_is_arc (finiteFormula x) (.internal c e)

theorem label_injective (x : SatTy.denote) :
    Function.Injective (fun cv : Fin x.length×Fin 12 => label x cv.1 cv.2) := by
  intro a b he
  have h := (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num_inj he
  simpa only [clause,Sum.inr.injEq,Sum.inl.injEq] using h

theorem key_injective (x : SatTy.denote) :
    Function.Injective (fun ce : Fin x.length×Fin 14 => (routeRecord x ce.1 ce.2).1) := by
  rintro ⟨c,e⟩ ⟨d,f⟩ he
  change (label x c (PlanarSatClause.Lattice.edge e).1,
    label x c (PlanarSatClause.Lattice.edge e).2)=
      (label x d (PlanarSatClause.Lattice.edge f).1,
        label x d (PlanarSatClause.Lattice.edge f).2) at he
  have hs := @label_injective x (c,(PlanarSatClause.Lattice.edge e).1)
    (d,(PlanarSatClause.Lattice.edge f).1) (congrArg (fun q : Nat×Nat => q.1) he)
  have ht := @label_injective x (c,(PlanarSatClause.Lattice.edge e).2)
    (d,(PlanarSatClause.Lattice.edge f).2) (congrArg (fun q : Nat×Nat => q.2) he)
  have hc : c=d := congrArg Prod.fst hs
  have hs' : (PlanarSatClause.Lattice.edge e).1=(PlanarSatClause.Lattice.edge f).1 :=
    congrArg (fun q : Fin x.length×Fin 12 => q.2) hs
  have ht' : (PlanarSatClause.Lattice.edge e).2=(PlanarSatClause.Lattice.edge f).2 :=
    congrArg (fun q : Fin x.length×Fin 12 => q.2) ht
  have hef : e=f := PlanarSatClause.Lattice.edge_injective (Prod.ext hs' ht')
  exact Prod.ext hc hef

theorem functional (x : SatTy.denote) : DirectedRouteLookupCode.Functional (routes.eval x) := by
  intro r hr s hs he
  obtain ⟨c,e,rfl⟩ := (mem_routes x r).mp hr
  obtain ⟨d,f,rfl⟩ := (mem_routes x s).mp hs
  have h := @key_injective x (c,e) (d,f) he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
  rfl

/-- Certified lookup composed with certified syntax-driven enumeration. -/
def lookup : Code (.pair SatTy DirectedRouteLookupCode.KeyTy) CycleInputTy :=
  .comp (.pair (.comp .fst routes) .snd) DirectedRouteLookupCode.code

theorem lookup_eval (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    lookup.eval (x,(routeRecord x c e).1)=(SatClauseOrder.route c e).map encodePoint := by
  change DirectedRouteLookupCode.code.eval (routes.eval x,(routeRecord x c e).1)=_
  apply DirectedRouteLookupCode.code_eq_of_mem
  · exact (mem_routes x _).mpr ⟨c,e,rfl⟩
  · exact functional x

/-- Every output route has the geometry already proved for the clause family. -/
theorem route_certificate (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    (SatClauseOrder.route c e).head?=some (SatClauseOrder.point c (PlanarSatClause.Lattice.edge e).1) ∧
    (SatClauseOrder.route c e).getLast?=some (SatClauseOrder.point c (PlanarSatClause.Lattice.edge e).2) ∧
    (SatClauseOrder.route c e).Nodup ∧
    (SatClauseOrder.route c e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2≤(SatClauseOrder.route c e).length ∧ (SatClauseOrder.route c e).length≤1073 :=
  SatClausePlacement.route_certificate (Fin.rev c) e

end GridHardness.SatClauseBodyCode
