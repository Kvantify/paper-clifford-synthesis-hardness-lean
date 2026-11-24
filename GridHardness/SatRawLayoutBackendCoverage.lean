/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRawLayoutBackendCode

/-!
# SAT Raw Layout Backend Coverage

The raw layout compiler is independent of catalogue order and repetitions.
Any lists containing exactly the actual vertex and edge records give the same
grid-point membership, regardless of their order or repeated entries.
-/

public section

namespace GridHardness.SatRawLayoutBackendCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

private theorem exists_map {α β : Type} (xs : List α) (f : α →β) (P : β →Prop) :
    (∃ y∈xs.map f,P y) ↔ ∃ x∈xs,P (f x) := by
  constructor
  · rintro ⟨y,hy,hp⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact ⟨x,hx,hp⟩
  · rintro ⟨x,hx,hp⟩
    exact ⟨f x,List.mem_map.mpr ⟨x,hx,rfl⟩,hp⟩

theorem code_mem (fs : List ClusterTy.denote) (es : List BipartiteRouteDataCode.InputTy.denote)
    (p : Point) :
    p∈GridPointCode.points (code.eval (fs,es)) ↔
      (∃ f∈fs,p∈rectanglePoints (SatLayoutBackendCode.cluster.eval (frame.eval f))) ∨
      (∃ e∈es,p∈GridPointCode.points
        (SatCompleteTentacleCode.code.eval (BipartiteRouteDataCode.code.eval e))) := by
  change p∈GridPointCode.points (SatLayoutBackendCode.code.eval
    (fs.map frame.eval,es.map BipartiteRouteDataCode.code.eval)) ↔ _
  rw [SatLayoutBackendCode.code_mem]
  exact or_congr (exists_map _ _ _) (exists_map _ _ _)

/-- Equal record membership suffices, even if the lists have different orders
or duplicate records. -/
theorem points_congr (z w : InputTy.denote)
    (hf : ∀ f, f∈z.1 ↔ f ∈w.1) (he : ∀ e, e∈z.2 ↔ e ∈w.2) :
    GridPointCode.points (code.eval z)=GridPointCode.points (code.eval w) := by
  rcases z with ⟨fs,es⟩
  rcases w with ⟨gs,ds⟩
  ext p
  rw [code_mem,code_mem]
  simp only [hf,he]

/-- Exact source-record coverage identifies the whole actual SAT grid without
any premise about the order in which a source program emits those records. -/
theorem points_of_coverage (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (z : InputTy.denote)
    (hf : ∀ f, f∈z.1 ↔ ∃ v : SatBipartiteDrawing.Vertex x,
      f =(encodePoint (SatBipartiteDrawing.point x hw v),
        decide (SatNineClusterPlacement.color x v =1)))
    (he : ∀ e, e∈z.2 ↔ ∃ a : SatDockCorridors.Edge x, e=SatBipartiteRouteCode.input x hw a) :
    GridPointCode.points (code.eval z)=(SatCompleteLayout.layout x hw).points := by
  have h := points_congr z (input x hw)
    (fun f => (hf f).trans (FiniteRecordLists.mem _ f).symm)
    (fun e => (he e).trans (FiniteRecordLists.mem _ e).symm)
  exact h.trans (points x hw)

end GridHardness.SatRawLayoutBackendCode
