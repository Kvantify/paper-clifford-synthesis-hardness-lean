/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetainedInterface
public import GridHardness.SatRowCoverage
public import GridHardness.SatColumnCoverage

/-!
# SAT Retained Coverage

Exhaustiveness of the simultaneous route catalogue at retained
crossings. Every missing local incidence is supplied by the neighboring
crossing, the actual extreme residual lane, or a clause/retirement link.
-/

public section

namespace GridHardness.SatRetainedCoverage
open CliffordComplexity PlanarSatAssembly CorrectedSatInterval SatRouteCatalogue
open SatRetainedInterface
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem fresh_ne (x : SatTy.denote) (c d : WireCrossingSchedule.Cell (permutation x))
    (h : d ≠ c) (u v : LocalVertex) : vertex x d u ≠ vertex x c v := by
  intro he
  have hd := congrArg (PermutationWirePlacement.decomposition (finiteFormula x) (permutation x)) he
  simp only [vertex,SatRetainedDrawing.vertex,PermutationWirePlacement.decomposition_fresh,
    Sum.inr.injEq,Prod.mk.injEq] at hd
  exact h hd.1

theorem retired_ne (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (i : Fin (3 *x.length)) (u : Fin 8) (v : LocalVertex) :
    PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inl (i,u)) ≠
      vertex x c v := by
  intro he
  have hd := congrArg (PermutationWirePlacement.decomposition (finiteFormula x) (permutation x)) he
  simp only [PermutationWirePlacement.vertex_original,PermutationWirePlacement.decomposition_original,
    vertex,SatRetainedDrawing.vertex,PermutationWirePlacement.decomposition_fresh] at hd
  cases hd

theorem row_zero_supplied (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (b : Bool) : Supplied x c (.inl false,b) := by
  rcases SatRowCoverage.last_or_next (permutation x) c.val.1 c.val.2 c.property with hl | ⟨k,hk⟩
  · let e : SatLastLinkDrawing.Edge (permutation x) := (⟨c.val,hl⟩,b)
    cases b
    · refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inl (c.val.2,4)),
        retired_ne x c c.val.2 4,?_⟩
      simpa only [e,SatLastLinkDrawing.source,SatLastLinkDrawing.target,
        SatLastLinkDrawing.sourceWire,SatLastLinkDrawing.targetWire,SatLastLinkDrawing.cell,
        Bool.false_eq_true,ite_false,ite_true,PermutationWirePlacement.vertex_fresh,
        vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,LastLinks.rowPort] using covers_last x e
    · refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inl (c.val.2,7)),
        retired_ne x c c.val.2 7,?_⟩
      simpa only [e,SatLastLinkDrawing.source,SatLastLinkDrawing.target,
        SatLastLinkDrawing.sourceWire,SatLastLinkDrawing.targetWire,SatLastLinkDrawing.cell,
        Bool.false_eq_true,ite_false,ite_true,PermutationWirePlacement.vertex_fresh,
        vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,LastLinks.rowPort] using covers_last x e
  · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(k,c.val.2),hk.2.1⟩
    have hdc : d ≠ c := by
      intro h
      have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) => z.val.1) h
      exact (ne_of_lt hk.2.2.1) he.symm
    let e : SatHorizontalDrawing.Edge (permutation x) := (⟨(c.val.1,k,c.val.2),hk⟩,!b)
    cases b
    · refine ⟨vertex x d (SatHorizontalDrawing.newPort true),
        fun v => fresh_ne x c d hdc _ v,?_⟩
      exact covers_horizontal x e
    · refine ⟨vertex x d (SatHorizontalDrawing.newPort false),
        fun v => fresh_ne x c d hdc _ v,?_⟩
      exact covers_horizontal x e

theorem false_port_supplied (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (b : Bool) : Supplied x c (.inl true,b) := by
  rcases SatRowCoverage.first_or_previous (permutation x) c.val.1 c.val.2 c.property with hf | ⟨k,hk⟩
  · let o := (SatWireLayout.variableRank (finiteFormula x)).symm c.val.2
    have ho : SatWireLayout.variableRank (finiteFormula x) o = c.val.2 :=
      (SatWireLayout.variableRank (finiteFormula x)).apply_symm_apply _
    have hw : SatClauseWireDrawing.actualWireVertex (finiteFormula x) o b =
        vertex x c (SatClauseWireDrawing.retainedPort b) := by
      simp only [SatClauseWireDrawing.actualWireVertex,ho,
        SatClauseWireDrawing.wireVertex_some _ _ _ _ hf,
        PermutationWirePlacement.vertex_fresh,vertex,SatRetainedDrawing.vertex]
    refine ⟨SatClauseWireDrawing.clauseVertex (finiteFormula x) o b,?_,?_⟩
    · intro v he
      have hd := congrArg (PermutationWirePlacement.decomposition (finiteFormula x) (permutation x)) he
      simp only [SatClauseWireDrawing.clauseVertex,SatClauseOrder.vertex,
        PermutationWirePlacement.decomposition_original,vertex,SatRetainedDrawing.vertex,
        PermutationWirePlacement.decomposition_fresh] at hd
      cases hd
    · have hc := covers_outer x (.inr (o,b))
      cases b <;> simpa only [SatOuterDrawing.source,SatOuterDrawing.target,
        SatClauseWireDrawing.source,SatClauseWireDrawing.target,Bool.false_eq_true,
        ite_false,ite_true,hw,At,stubIncoming,stubVertex,Bool.not_false,Bool.not_true] using hc
  · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(k,c.val.2),hk.1⟩
    have hdc : d ≠ c := by
      intro h
      have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) => z.val.1) h
      exact (ne_of_lt hk.2.2.1) he
    let e : SatHorizontalDrawing.Edge (permutation x) := (⟨(k,c.val.1,c.val.2),hk⟩,!b)
    cases b
    · refine ⟨vertex x d (SatHorizontalDrawing.oldPort true),
        fun v => fresh_ne x c d hdc _ v,?_⟩
      exact covers_horizontal x e
    · refine ⟨vertex x d (SatHorizontalDrawing.oldPort false),
        fun v => fresh_ne x c d hdc _ v,?_⟩
      exact covers_horizontal x e

theorem row_supplied (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (r : Fin 4) (b : Bool) : Supplied x c (.inr r,b) := by
  by_cases hr : r.val%2=0
  · cases b
    · rcases SatColumnCoverage.upper (permutation x) c.val.1 c.val.2 c.property with hf | ⟨k,hk⟩
      · let e : SatResidualDrawing.Edge (permutation x) := ⟨c.val.1,r,.above c.val.2 hf⟩
        refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x)
            (.inl (c.val.1,SatCrossingRetirement.falseVertex r)),
          retired_ne x c c.val.1 _ ,?_⟩
        simpa only [e,SatResidualDrawing.source,SatResidualDrawing.target,
          SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          PermutationWirePlacement.vertex_fresh,vertex,SatRetainedDrawing.vertex,
          stubVertex,stubIncoming,At,SatResidualDrawing.input,SatResidualDrawing.output,
          XorLine.inputPort,XorLine.outputPort] using covers_residual x e
      · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(c.val.1,k),hk.2.1⟩
        have hdc : d ≠ c := by
          intro h
          have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) =>
            permutation x z.val.2) h
          exact (ne_of_lt hk.2.2.1) he.symm
        let e : SatVerticalDrawing.Edge (permutation x) := (⟨(c.val.1,c.val.2,k),hk⟩,r)
        refine ⟨vertex x d (SatVerticalDrawing.outputPort r),
          fun v => fresh_ne x c d hdc _ v,?_⟩
        simpa only [e,SatVerticalDrawing.source,SatVerticalDrawing.target,
          SatVerticalDrawing.endpoints,SatVerticalDrawing.lowerCell,SatVerticalDrawing.upperCell,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,
          SatVerticalDrawing.inputPort,SatVerticalDrawing.outputPort,
          XorLine.inputPort,XorLine.outputPort] using covers_vertical x e
    · rcases SatColumnCoverage.lower (permutation x) c.val.1 c.val.2 c.property with hf | ⟨k,hk⟩
      · let e : SatResidualDrawing.Edge (permutation x) := ⟨c.val.1,r,.below c.val.2 hf⟩
        refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x)
            (.inl (c.val.1,SatCrossingRetirement.trueVertex r)),
          retired_ne x c c.val.1 _ ,?_⟩
        simpa only [e,SatResidualDrawing.source,SatResidualDrawing.target,
          SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          PermutationWirePlacement.vertex_fresh,vertex,SatRetainedDrawing.vertex,
          stubVertex,stubIncoming,At,SatResidualDrawing.input,SatResidualDrawing.output,
          XorLine.inputPort,XorLine.outputPort] using covers_residual x e
      · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(c.val.1,k),hk.1⟩
        have hdc : d ≠ c := by
          intro h
          have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) =>
            permutation x z.val.2) h
          exact (ne_of_lt hk.2.2.1) he
        let e : SatVerticalDrawing.Edge (permutation x) := (⟨(c.val.1,k,c.val.2),hk⟩,r)
        refine ⟨vertex x d (SatVerticalDrawing.inputPort r),
          fun v => fresh_ne x c d hdc _ v,?_⟩
        simpa only [e,SatVerticalDrawing.source,SatVerticalDrawing.target,
          SatVerticalDrawing.endpoints,SatVerticalDrawing.lowerCell,SatVerticalDrawing.upperCell,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,
          SatVerticalDrawing.inputPort,SatVerticalDrawing.outputPort,
          XorLine.inputPort,XorLine.outputPort] using covers_vertical x e
  · cases b
    · rcases SatColumnCoverage.lower (permutation x) c.val.1 c.val.2 c.property with hf | ⟨k,hk⟩
      · let e : SatResidualDrawing.Edge (permutation x) := ⟨c.val.1,r,.below c.val.2 hf⟩
        refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x)
            (.inl (c.val.1,SatCrossingRetirement.trueVertex r)),
          retired_ne x c c.val.1 _ ,?_⟩
        simpa only [e,SatResidualDrawing.source,SatResidualDrawing.target,
          SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          PermutationWirePlacement.vertex_fresh,vertex,SatRetainedDrawing.vertex,
          stubVertex,stubIncoming,At,SatResidualDrawing.input,SatResidualDrawing.output,
          XorLine.inputPort,XorLine.outputPort] using covers_residual x e
      · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(c.val.1,k),hk.1⟩
        have hdc : d ≠ c := by
          intro h
          have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) =>
            permutation x z.val.2) h
          exact (ne_of_lt hk.2.2.1) he
        let e : SatVerticalDrawing.Edge (permutation x) := (⟨(c.val.1,k,c.val.2),hk⟩,r)
        refine ⟨vertex x d (SatVerticalDrawing.outputPort r),
          fun v => fresh_ne x c d hdc _ v,?_⟩
        simpa only [e,SatVerticalDrawing.source,SatVerticalDrawing.target,
          SatVerticalDrawing.endpoints,SatVerticalDrawing.lowerCell,SatVerticalDrawing.upperCell,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,
          SatVerticalDrawing.inputPort,SatVerticalDrawing.outputPort,
          XorLine.inputPort,XorLine.outputPort] using covers_vertical x e
    · rcases SatColumnCoverage.upper (permutation x) c.val.1 c.val.2 c.property with hf | ⟨k,hk⟩
      · let e : SatResidualDrawing.Edge (permutation x) := ⟨c.val.1,r,.above c.val.2 hf⟩
        refine ⟨PermutationWirePlacement.vertex (finiteFormula x) (permutation x)
            (.inl (c.val.1,SatCrossingRetirement.falseVertex r)),
          retired_ne x c c.val.1 _ ,?_⟩
        simpa only [e,SatResidualDrawing.source,SatResidualDrawing.target,
          SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          PermutationWirePlacement.vertex_fresh,vertex,SatRetainedDrawing.vertex,
          stubVertex,stubIncoming,At,SatResidualDrawing.input,SatResidualDrawing.output,
          XorLine.inputPort,XorLine.outputPort] using covers_residual x e
      · let d : WireCrossingSchedule.Cell (permutation x) := ⟨(c.val.1,k),hk.2.1⟩
        have hdc : d ≠ c := by
          intro h
          have he := congrArg (fun z : WireCrossingSchedule.Cell (permutation x) =>
            permutation x z.val.2) h
          exact (ne_of_lt hk.2.2.1) he.symm
        let e : SatVerticalDrawing.Edge (permutation x) := (⟨(c.val.1,c.val.2,k),hk⟩,r)
        refine ⟨vertex x d (SatVerticalDrawing.inputPort r),
          fun v => fresh_ne x c d hdc _ v,?_⟩
        simpa only [e,SatVerticalDrawing.source,SatVerticalDrawing.target,
          SatVerticalDrawing.endpoints,SatVerticalDrawing.lowerCell,SatVerticalDrawing.upperCell,
          hr,ite_true,ite_false,Bool.false_eq_true,Bool.not_false,Bool.not_true,
          vertex,SatRetainedDrawing.vertex,stubVertex,stubIncoming,At,
          SatVerticalDrawing.inputPort,SatVerticalDrawing.outputPort,
          XorLine.inputPort,XorLine.outputPort] using covers_vertical x e

/-- Every actual arc entering or leaving any retained crossing vertex has
an index in the combined route catalogue. -/
theorem complete (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (v : LocalVertex) : LocalComplete x (vertex x c v) := by
  apply complete_of_supplied x c
  rintro ⟨(a | r),b⟩
  · cases a
    · exact row_zero_supplied x c b
    · exact false_port_supplied x c b
  · exact row_supplied x c r b

end GridHardness.SatRetainedCoverage
