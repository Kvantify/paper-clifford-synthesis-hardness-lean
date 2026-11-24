/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRouteCatalogue

/-!
# SAT Retained Interface

The retained forty-vertex crossing has twelve missing directed
incidences. Supplying those external interfaces saturates its degree-three
bound and therefore covers every actual arc at every retained vertex.
-/

@[expose] public section

namespace GridHardness.SatRetainedInterface
open CliffordComplexity PlanarSatAssembly CorrectedSatInterval SatRouteCatalogue
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev LocalVertex := SatCrossingHorizontal.RetainedVertex
abbrev Stub := (Bool ⊕ Fin 4) × Bool

/-- The removed section-zero attachment, false side port, and four row
ports. The second component distinguishes their two directed ends. -/
def stubVertex : Stub → LocalVertex
  | (.inl false,b) => ⟨XorLine.row 0 b,trivial⟩
  | (.inl true,b) => SatClauseWireDrawing.retainedPort b
  | (.inr r,b) => ⟨XorLine.row r b,trivial⟩

def stubIncoming : Stub → Bool
  | (.inl false,b) => b
  | (_,b) => !b

abbrev Neighbor := LocalVertex ⊕ Stub
def LocalAt (v : LocalVertex) : Neighbor ⊕ Neighbor → Prop
  | .inl (.inl u) => XorLine.Adj 4 u.val v.val
  | .inr (.inl u) => XorLine.Adj 4 v.val u.val
  | .inl (.inr s) => stubVertex s = v ∧ stubIncoming s = true
  | .inr (.inr s) => stubVertex s = v ∧ stubIncoming s = false

instance (v : LocalVertex) (z : Neighbor ⊕ Neighbor) : Decidable (LocalAt v z) := by
  rcases z with (u | s) | (u | s) <;> unfold LocalAt <;> infer_instance

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem local_card : ∀ v : LocalVertex,
    Fintype.card {z : Neighbor ⊕ Neighbor // LocalAt v z} = 3 := by
  decide +kernel

private theorem stub_unique : ∀ s t : Stub,
    stubVertex s = stubVertex t → stubIncoming s = stubIncoming t → s = t := by
  decide +kernel

noncomputable def vertex (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (v : LocalVertex) : Vertex x := SatRetainedDrawing.vertex (finiteFormula x) (permutation x) (c,v)

theorem vertex_injective (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x)) :
    Function.Injective (vertex x c) := by
  intro u v h
  have hh := congrArg (PermutationWirePlacement.decomposition (finiteFormula x) (permutation x)) h
  simpa only [vertex,SatRetainedDrawing.vertex,PermutationWirePlacement.decomposition_fresh,
    Sum.inr.injEq,Prod.mk.injEq,true_and] using hh

theorem local_covers (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x))
    (u v : LocalVertex) (h : XorLine.Adj 4 u.val v.val) :
    Covers x (vertex x c u) (vertex x c v) := by
  obtain ⟨e,he⟩ := (SatRetainedDrawing.local_adj_iff u v).mp h
  have hc := covers_retained x (c,e)
  simpa only [SatRetainedDrawing.source,SatRetainedDrawing.target,
    SatRetainedDrawing.endpoints,he,vertex] using hc

/-- A missing interface is supplied by a catalogued arc whose other
endpoint is outside the retained cell. -/
def Supplied (x : SatTy.denote) (c : WireCrossingSchedule.Cell (permutation x)) (s : Stub) : Prop :=
  ∃ w : Vertex x, (∀ v, w ≠ vertex x c v) ∧
    At x (vertex x c (stubVertex s)) (if stubIncoming s then .inl w else .inr w)

theorem complete_of_supplied (x : SatTy.denote)
    (c : WireCrossingSchedule.Cell (permutation x)) (hs : ∀ s, Supplied x c s)
    (v : LocalVertex) : LocalComplete x (vertex x c v) := by
  classical
  let w (s : Stub) := (hs s).choose
  have hw (s : Stub) := (hs s).choose_spec
  let f : Neighbor → Vertex x := Sum.elim (vertex x c) w
  let g : {z : Neighbor ⊕ Neighbor // LocalAt v z} → Vertex x ⊕ Vertex x :=
    fun z => Sum.map f f z.val
  have hg : Function.Injective g := by
    intro a b he
    apply Subtype.ext
    rcases a with ⟨(a | a),ha⟩ <;> rcases b with ⟨(b | b),hb⟩
    all_goals dsimp [g] at he
    · apply congrArg Sum.inl
      have he := Sum.inl.inj he
      rcases a with (a | a) <;> rcases b with (b | b)
      · exact congrArg Sum.inl (vertex_injective x c he)
      · exact False.elim ((hw b).1 a he.symm)
      · exact False.elim ((hw a).1 b he)
      · exact congrArg Sum.inr (stub_unique a b (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm))
    · cases he
    · cases he
    · apply congrArg Sum.inr
      have he := Sum.inr.inj he
      rcases a with (a | a) <;> rcases b with (b | b)
      · exact congrArg Sum.inl (vertex_injective x c he)
      · exact False.elim ((hw b).1 a he.symm)
      · exact False.elim ((hw a).1 b he)
      · exact congrArg Sum.inr (stub_unique a b (ha.1.trans hb.1.symm) (ha.2.trans hb.2.symm))
  have hc (z : {z : Neighbor ⊕ Neighbor // LocalAt v z}) : At x (vertex x c v) (g z) := by
    rcases z with ⟨(u | s) | (u | s),hz⟩
    · exact local_covers x c u v hz
    · have h := (hw s).2
      simpa only [g,f,w,Sum.map,Sum.elim,Function.comp_apply,Sum.elim_inr,hz.1,hz.2,ite_true] using h
    · exact local_covers x c v u hz
    · have h := (hw s).2
      simpa only [g,f,w,Sum.map,Sum.elim,Function.comp_apply,Sum.elim_inr,hz.1,hz.2,Bool.false_eq_true,ite_false] using h
  let e := (Fintype.equivFinOfCardEq (local_card v)).symm
  exact complete_of_three x (vertex x c v) (g ∘ e) (hg.comp e.injective) (fun i => hc (e i))

end GridHardness.SatRetainedInterface
