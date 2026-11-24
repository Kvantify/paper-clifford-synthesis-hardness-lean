/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableBodyCatalogue
public import GridHardness.SatClauseBodyCatalogue
public import GridHardness.SatClauseBackboneCode
public import GridHardness.SatVariableChainCatalogue
public import GridHardness.SatExteriorRecordsCode
public import GridHardness.SatClauseLinkRecordsCode
public import GridHardness.SatRetainedDrawingCatalogue
public import GridHardness.SatIntercellCatalogueCode
public import GridHardness.SatRetiredDrawingCatalogue
public import GridHardness.SatLastLinkCode
public import GridHardness.SatResidualDrawingCode

/-!
# SAT Drawing Catalogue Code

A complete syntax-driven catalogue of the final directed SAT drawing.
Every emitted record is an existing catalogue route, and every catalogue
route is emitted. Both execution and the entire serialized output have
polynomial bounds in the original SAT syntax.
-/

@[expose] public section

namespace GridHardness.SatDrawingCatalogueCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

attribute [local irreducible] SatVariableBodyCode.code SatClauseBodyCode.routes
  SatClauseBackboneCode.code SatVariableChainRecordsCode.code SatExteriorRecordsCode.code
  SatClauseLinkRecordsCode.code SatRetainedDrawingCode.routes SatIntercellCatalogueCode.routes
  SatRetiredDrawingCode.routes SatLastLinkCode.code SatResidualDrawingCode.routes

abbrev RecordTy := DirectedRouteLookupCode.RecordTy
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy
noncomputable abbrev catalogueRecord := SatIntercellCatalogueCode.catalogueRecord

/-- All eleven families, including the empty-column residual cases. -/
def code : Code SatTy RoutesTy :=
  Code.append SatVariableBodyCode.code
    (Code.append SatClauseBodyCode.routes
    (Code.append SatClauseBackboneCode.code
    (Code.append SatVariableChainRecordsCode.code
    (Code.append SatExteriorRecordsCode.code
    (Code.append SatClauseLinkRecordsCode.code
    (Code.append SatRetainedDrawingCode.routes
    (Code.append SatIntercellCatalogueCode.routes
    (Code.append SatRetiredDrawingCode.routes
    (Code.append SatLastLinkCode.code
    (SatResidualDrawingCode.routes))))))))))

theorem mem_programs (x : SatTy.denote) (r : RecordTy.denote) : r∈code.eval x ↔
    r∈SatVariableBodyCode.code.eval x ∨
    r∈SatClauseBodyCode.routes.eval x ∨
    r∈SatClauseBackboneCode.code.eval x ∨
    r∈SatVariableChainRecordsCode.code.eval x ∨
    r∈SatExteriorRecordsCode.code.eval x ∨
    r∈SatClauseLinkRecordsCode.code.eval x ∨
    r∈SatRetainedDrawingCode.routes.eval x ∨
    r∈SatIntercellCatalogueCode.routes.eval x ∨
    r∈SatRetiredDrawingCode.routes.eval x ∨
    r∈SatLastLinkCode.code.eval x ∨
    r∈SatResidualDrawingCode.routes.eval x := by
  rw [code]
  simp only [append_eval,List.mem_append]

theorem mem_code (x : SatTy.denote) (r : RecordTy.denote) :
    r∈code.eval x ↔ ∃e : SatWireDrawingGeometry.Edge x,r=catalogueRecord x e := by
  rw [mem_programs,SatVariableBodyCode.mem_code,SatClauseBodyCode.mem_routes,
    SatClauseBackboneCode.mem_code,SatVariableChainRecordsCode.mem_code,
    SatExteriorRecordsCode.mem_code,SatClauseLinkRecordsCode.mem_code,
    SatRetainedDrawingCode.mem_routes,SatIntercellCatalogueCode.mem_routes,
    SatRetiredDrawingCode.mem_routes,SatLastLinkCode.mem_code,SatResidualDrawingCode.mem_routes]
  constructor
  · rintro (⟨e,hr⟩ | ⟨c,e,hr⟩ | ⟨c,d,hd,hr⟩ | ⟨e,hr⟩ | ⟨e,hr⟩ |
      ⟨j,b,hr⟩ | ⟨c,e,hr⟩ | ⟨e,hr⟩ | ⟨j,e,hr⟩ | ⟨c,b,hr⟩ | ⟨e,hr⟩)
    · exact ⟨SatVariableBodyCode.catalogueIndex x e,hr.trans (SatVariableBodyCode.record_actual x e)⟩
    · exact ⟨SatClauseBodyCode.catalogueIndex x c e,hr.trans (SatClauseBodyCode.routeRecord_actual x c e)⟩
    · exact ⟨SatClauseBackboneCode.catalogueIndex x c d hd,hr.trans (SatClauseBackboneCode.record_actual x c d hd)⟩
    · exact ⟨SatVariableChainRecordsCode.catalogueIndex x e,hr.trans (SatVariableChainRecordsCode.record_actual x e)⟩
    · exact ⟨SatExteriorRecordsCode.catalogueIndex x e,hr.trans (SatExteriorRecordsCode.record_actual x e)⟩
    · exact ⟨SatClauseLinkRecordsCode.catalogueIndex x j b,hr.trans (SatClauseLinkRecordsCode.record_actual x j b)⟩
    · exact ⟨SatRetainedDrawingCode.catalogueIndex x c e,hr.trans (SatRetainedDrawingCode.routeRecord_actual x c e)⟩
    · exact ⟨SatIntercellCatalogueCode.catalogueIndex x e,hr.symm⟩
    · exact ⟨SatRetiredDrawingCode.catalogueIndex x j e,hr.trans (SatRetiredDrawingCode.routeRecord_actual x j e)⟩
    · exact ⟨SatLastLinkCode.catalogueIndex x c b,hr⟩
    · exact ⟨SatResidualDrawingCode.catalogueIndex x e,hr.symm⟩
  · rintro ⟨e,rfl⟩
    rcases e with e | e
    · rcases e with e | e
      · rcases e with e | ⟨c,b⟩
        · rcases e with e | ⟨j,e⟩
          · rcases e with e | e
            · rcases e with e | ⟨c,e⟩
              · rcases e with e | ⟨o,b⟩
                · rcases e with e | e
                  · rcases e with e | e
                    · exact Or.inl (⟨e,(SatVariableBodyCode.record_actual x e).symm⟩)
                    · cases e with
                      | internal c e =>
                        exact Or.inr (Or.inl (⟨c,e,(SatClauseBodyCode.routeRecord_actual x c e).symm⟩))
                      | backbone c d hd =>
                        exact Or.inr (Or.inr (Or.inl (⟨c,d,hd,(SatClauseBackboneCode.record_actual x c d hd).symm⟩)))
                  · rcases e with e | e
                    · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨e,(SatVariableChainRecordsCode.record_actual x e).symm⟩))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨e,(SatExteriorRecordsCode.record_actual x e).symm⟩)))))
                · let j := SatWireLayout.variableRank (finiteFormula x) o
                  have he : SatClauseLinkRecordsCode.occurrence x j=o :=
                    (SatWireLayout.variableRank (finiteFormula x)).symm_apply_apply o
                  have hr := SatClauseLinkRecordsCode.record_actual x j b
                  simp only [SatClauseLinkRecordsCode.catalogueIndex,he] at hr
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j,b,hr.symm⟩))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨c,e,(SatRetainedDrawingCode.routeRecord_actual x c e).symm⟩)))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.inl e,rfl⟩))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨j,e,(SatRetiredDrawingCode.routeRecord_actual x j e).symm⟩)))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨c,b,rfl⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨.inr e,rfl⟩))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨e,rfl⟩))))))))))

/-- Completeness does not require an external promise about the input width. -/
theorem catalogue_covered (x : SatTy.denote) (e : SatWireDrawingGeometry.Edge x) :
    catalogueRecord x e∈code.eval x := (mem_code x _).mpr ⟨e,rfl⟩

end GridHardness.SatDrawingCatalogueCode
