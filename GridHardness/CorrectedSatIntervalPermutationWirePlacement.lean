/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingWireVertices
public import GridHardness.CorrectedSatIntervalPermutationGraph

/-!
# Corrected SAT Interval Permutation Wire Placement

Identify every occurrence-XOR vertex and retained crossing vertex in
the sweep for an arbitrary height permutation. The remaining sentinel,
variable and clause vertices form an explicit disjoint body family.
Coordinates here place vertices only; no global edge drawing is asserted.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.PermutationWirePlacement
open PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Convert the actual chronological trace cells to geometric inversion
cells, preserving both wire indices. -/
def traceCellEquiv {N : Nat} (p : Equiv.Perm (Fin N)) :
    {c : Nat × Nat // c∈trace (permutationHeight p) N 0} ≃ WireCrossingSchedule.Cell p where
  toFun c := by
    have hc := (mem_trace _ _ _ c.val).mp c.property
    have hi : c.val.1<N := by omega
    have hj : c.val.2<N := by omega
    exact ⟨(⟨c.val.1,hi⟩,⟨c.val.2,hj⟩),
      (PermutationGraph.covers_inversion p ⟨c.val.1,hi⟩ ⟨c.val.2,hj⟩).mp c.property⟩
  invFun c := ⟨(c.val.1.val,c.val.2.val),
    (PermutationGraph.covers_inversion p c.val.1 c.val.2).mpr c.property⟩
  left_inv c := Subtype.ext rfl
  right_inv c := Subtype.ext rfl

/-- The inverse uses the real crossing's position in the insertion trace,
not an arbitrary enumeration of a finite set. -/
noncomputable def crossingEquiv {N : Nat} (p : Equiv.Perm (Fin N)) :
    Fin (moveCount (permutationHeight p) N 0) ≃ WireCrossingSchedule.Cell p :=
  (GlobalNumbering.traceEquiv (permutationHeight p) N 0).trans (traceCellEquiv p)

theorem crossingEquiv_symm_val {N : Nat} (p : Equiv.Perm (Fin N))
    (c : WireCrossingSchedule.Cell p) :
    ((crossingEquiv p).symm c).val=
      (trace (permutationHeight p) N 0).idxOf (c.val.1.val,c.val.2.val) := by
  have hh := congrArg (fun z : WireCrossingSchedule.Cell p => (z.val.1.val,z.val.2.val))
    ((crossingEquiv p).apply_symm_apply c)
  change (GlobalNumbering.traceEquiv (permutationHeight p) N 0
    ((crossingEquiv p).symm c)).val=(c.val.1.val,c.val.2.val) at hh
  rw [GlobalNumbering.traceEquiv_val] at hh
  rw [← hh]
  exact ((trace_nodup (permutationHeight p) N 0).idxOf_getElem
    ((crossingEquiv p).symm c).val (by rw [trace_length]; exact
      ((crossingEquiv p).symm c).isLt)).symm

variable {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

/-- Exact provenance of all vertices after the chosen permutation sweep. -/
noncomputable def decomposition :
    (PermutationGraph.graph φ p).Vertex ≃
      PlanarSatAssembly.Vertex n m ⊕
        (WireCrossingSchedule.Cell p × SatCrossingHorizontal.RetainedVertex) :=
  (GlobalNumbering.decomposition (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (3+2*n+36*m)
    (initialState φ) (PermutationGraph.initial_ready φ p) (GlobalNumbering.initialEquiv φ)).trans
      (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (crossingEquiv p) (Equiv.refl _)))

theorem decomposition_original (v : PlanarSatAssembly.Vertex n m) :
    decomposition φ p (PermutationGraph.liftOriginal φ p v)=.inl v := by
  change (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr (crossingEquiv p) (Equiv.refl _)))
    (GlobalNumbering.decomposition _ _ _ _ _ _ _ _ _
      (GlobalNumbering.runLift _ _ _ _ _ (initialState φ) _ v))=_
  rw [GlobalNumbering.decomposition_old]
  rfl

noncomputable def fresh (c : WireCrossingSchedule.Cell p)
    (v : SatCrossingHorizontal.RetainedVertex) : (PermutationGraph.graph φ p).Vertex :=
  GlobalNumbering.runFresh (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    ((crossingEquiv p).symm c) v

theorem decomposition_fresh (c : WireCrossingSchedule.Cell p)
    (v : SatCrossingHorizontal.RetainedVertex) :
    decomposition φ p (fresh φ p c v)=.inr (c,v) := by
  change (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr (crossingEquiv p) (Equiv.refl _)))
    (GlobalNumbering.decomposition _ _ _ _ _ _ _ _ _
      (GlobalNumbering.runFresh _ _ _ _ _ _ _ ((crossingEquiv p).symm c) v))=_
  rw [GlobalNumbering.decomposition_fresh]
  change Sum.inr ((crossingEquiv p) ((crossingEquiv p).symm c),v)=_
  rw [Equiv.apply_symm_apply]

theorem fresh_names (c : WireCrossingSchedule.Cell p)
    (v : SatCrossingHorizontal.RetainedVertex) :
    (PermutationGraph.number φ p (fresh φ p c v)).val=
      3+2*n+36*m+40*(trace (permutationHeight p) (3*m) 0).idxOf (c.val.1.val,c.val.2.val)+
        (Numbering.retainedIndex v).val := by
  change (GlobalNumbering.runEquiv _ _ _ _ _ _ _ _ _
    (GlobalNumbering.runFresh _ _ _ _ _ _ _ _ _)).val=_
  rw [GlobalNumbering.runFresh_names,crossingEquiv_symm_val]

abbrev WireVertex := SatCrossingWireVertices.Vertex p

def names : WireVertex p →
    PlanarSatAssembly.Vertex n m ⊕
      (WireCrossingSchedule.Cell p × SatCrossingHorizontal.RetainedVertex)
  | .inl (j,v) => .inl (xor ((SatWireLayout.variableRank φ).symm j) v)
  | .inr (c,v) => .inr (c,v)

theorem names_injective : Function.Injective (names φ p) := by
  intro u v he
  cases u with
  | inl jv =>
    cases v with
    | inl kw =>
      have h := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj he)))
      exact congrArg Sum.inl (Prod.ext
        ((SatWireLayout.variableRank φ).symm.injective (congrArg Prod.fst h))
        (Prod.mk.inj h).2)
    | inr cv => cases he
  | inr cv =>
    cases v with
    | inl jv => cases he
    | inr dw => exact congrArg Sum.inr (Sum.inr.inj he)

noncomputable def vertex (v : WireVertex p) : (PermutationGraph.graph φ p).Vertex :=
  (decomposition φ p).symm (names φ p v)

theorem vertex_injective : Function.Injective (vertex φ p) :=
  (decomposition φ p).symm.injective.comp (names_injective φ p)

theorem vertex_names (v : WireVertex p) :
    decomposition φ p (vertex φ p v)=names φ p v :=
  (decomposition φ p).apply_symm_apply _

theorem vertex_original (j : Fin (3 *m)) (v : Fin 8) :
    vertex φ p (.inl (j,v))=
      PermutationGraph.liftOriginal φ p (xor ((SatWireLayout.variableRank φ).symm j) v) := by
  apply (decomposition φ p).injective
  rw [vertex_names,decomposition_original]
  rfl

theorem vertex_occurrence (o : Occurrence m) (v : Fin 8) :
    vertex φ p (.inl (SatWireLayout.variableRank φ o,v))=
      PermutationGraph.liftOriginal φ p (xor o v) := by
  rw [vertex_original,Equiv.symm_apply_apply]

theorem vertex_fresh (c : WireCrossingSchedule.Cell p)
    (v : SatCrossingHorizontal.RetainedVertex) :
    vertex φ p (.inr (c,v))=fresh φ p c v := by
  apply (decomposition φ p).injective
  rw [vertex_names,decomposition_fresh]
  rfl

def point (v : WireVertex p) : Int × Int := SatCrossingWireVertices.point p v

theorem point_injective : Function.Injective (point p) :=
  SatCrossingWireVertices.point_injective _

theorem same_point_iff_same_vertex (u v : WireVertex p) :
    point p u=point p v ↔ vertex φ p u=vertex φ p v := by
  constructor
  · intro h
    exact congrArg (vertex φ p) (point_injective p h)
  · intro h
    exact congrArg (point p) (vertex_injective φ p h)

theorem point_bounds (v : WireVertex p) :
    0≤(point p v).1 ∧ (point p v).1≤512*(3*m+1)+65 ∧
      0≤(point p v).2 ∧ (point p v).2≤1024*(3*m)+522 :=
  SatCrossingWireVertices.point_bounds _ _

/-- The body family keeps the finite sentinel, variable, and clause tags.
It excludes exactly the occurrence XORs. -/
abbrev BodyVertex (n m : Nat) := Fin 3 ⊕ ((Fin n × Bool) ⊕ (Fin m × Fin 12))

def bodyNames : BodyVertex n m → PlanarSatAssembly.Vertex n m
  | .inl i => sent i
  | .inr (.inl (v,b)) => var v b
  | .inr (.inr (c,v)) => clause c v

theorem bodyNames_injective : Function.Injective (bodyNames (n:=n) (m:=m)) := by
  intro a b he
  rcases a with i | ⟨v,t⟩ | ⟨c,v⟩ <;> rcases b with j | ⟨w,u⟩ | ⟨d,w⟩
  all_goals simp only [bodyNames,sent,var,clause,Sum.inl.injEq,Sum.inr.injEq,
    reduceCtorEq] at he ⊢
  all_goals exact he

theorem bodyNames_ne_xor (b : BodyVertex n m) (o : Occurrence m) (v : Fin 8) :
    bodyNames b≠xor o v := by
  rcases b with i | ⟨w,t⟩ | ⟨c,u⟩ <;>
    simp [bodyNames,sent,var,clause,PlanarSatAssembly.xor]

noncomputable def bodyVertex (b : BodyVertex n m) : (PermutationGraph.graph φ p).Vertex :=
  PermutationGraph.liftOriginal φ p (bodyNames b)

theorem bodyVertex_injective : Function.Injective (bodyVertex φ p) :=
  (PermutationGraph.liftOriginal_injective φ p).comp bodyNames_injective

theorem bodyVertex_names (b : BodyVertex n m) :
    decomposition φ p (bodyVertex φ p b)=.inl (bodyNames b) :=
  decomposition_original φ p _

theorem body_ne_wire (b : BodyVertex n m) (v : WireVertex p) :
    bodyVertex φ p b≠vertex φ p v := by
  intro h
  have hn := congrArg (decomposition φ p) h
  rw [bodyVertex_names,vertex_names] at hn
  cases v with
  | inl jv => exact bodyNames_ne_xor b _ _ (Sum.inl.inj hn)
  | inr cv => cases hn

theorem names_cover (z : PlanarSatAssembly.Vertex n m ⊕
    (WireCrossingSchedule.Cell p × SatCrossingHorizontal.RetainedVertex)) :
    (∃ b : BodyVertex n m, Sum.inl (bodyNames b)=z) ∨ ∃ v, names φ p v=z := by
  rcases z with z | ⟨c,v⟩
  · rcases z with i | ⟨w,t⟩ | ⟨c,v⟩ | ⟨o,v⟩
    · exact Or.inl ⟨.inl i,rfl⟩
    · exact Or.inl ⟨.inr (.inl (w,t)),rfl⟩
    · exact Or.inl ⟨.inr (.inr (c,v)),rfl⟩
    · refine Or.inr ⟨.inl (SatWireLayout.variableRank φ o,v),?_⟩
      simp only [names,Equiv.symm_apply_apply,PlanarSatAssembly.xor]
  · exact Or.inr ⟨.inr (c,v),rfl⟩

/-- These disjoint families exhaust the actual sweep graph: body vertices,
all eight names of every occurrence XOR, and all forty retained names of
every executed crossing. -/
theorem vertex_cases (v : (PermutationGraph.graph φ p).Vertex) :
    (∃ b, bodyVertex φ p b=v) ∨ ∃ w, vertex φ p w=v := by
  rcases names_cover φ p (decomposition φ p v) with ⟨b,hb⟩ | ⟨w,hw⟩
  · refine Or.inl ⟨b,(decomposition φ p).injective ?_⟩
    rw [bodyVertex_names]
    exact hb
  · refine Or.inr ⟨w,(decomposition φ p).injective ?_⟩
    rw [vertex_names]
    exact hw

end GridHardness.CorrectedSatInterval.PermutationWirePlacement
