/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalNumbering

/-!
# Corrected SAT Interval Numbered Adjacency

A direct adjacency table for a crossing, using the eight old
active XOR names again and adding only forty new names. All quantifiers in
this table range over fixed finite gadgets; it does not inspect the inverse
of a graph isomorphism.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.NumberedAdjacency
open XorLineRegistry XorLineSchedule XorLine

abbrev Fresh := SatCrossingHorizontal.RetainedVertex

section Table
variable {V : Type*}

/-- The old names outside the active XOR. -/
def Outside (e : Fin 8 → V) (v : V) : Prop := ∀ j, e j ≠ v

/-- Reuse the original eight names for the refreshed section zero. -/
def tileName (e : Fin 8 → V) (v : XorLine.Vertex 4) : V ⊕ Fresh :=
  match Numbering.tileEquiv v with
  | .inl j => .inl (e j)
  | .inr w => .inr w

@[simp] theorem tileName_active (e : Fin 8 → V) (j : Fin 8) :
    tileName e (x 0 j) = .inl (e j) := rfl

@[simp] theorem tileName_retained (e : Fin 8 → V) (v : Fresh) :
    tileName e v.val = .inr v := by
  simp [tileName, Numbering.tileEquiv_retained]

@[simp] theorem not_outside_active (e : Fin 8 → V) (j : Fin 8) :
    ¬Outside e (e j) := fun h => h j rfl

/-- Old arcs survive unless they are one of the four subdivided bundle
arcs or the false external boundary. The ten internal XOR arcs are retained. -/
def oldOld (D : V → V → Prop) (e : Fin 8 → V) (source target : Fin 4 → V)
    (u v : V) : Prop :=
  (Outside e u ∧ Outside e v ∧ D u v ∧ ¬∃ i, u = source i ∧ v = target i) ∨
  (Outside e u ∧ v = e 3 ∧ D u v) ∨
  (u = e 0 ∧ Outside e v ∧ D u v) ∨
  ∃ i j, u = e i ∧ v = e j ∧ ∃ k : Fin 10, XorGadget.arc k = (i,j)

/-- Edges entering a new retained cell come from the old false boundary,
the four subdivided bundle sources, or the refreshed section zero. -/
def oldFresh (D : V → V → Prop) (e : Fin 8 → V) (source : Fin 4 → V)
    (u : V) (v : Fresh) : Prop :=
  (Outside e u ∧ ((D u (e 4) ∧ v.val = inputPort 4 (.inl false)) ∨
    ∃ i, u = source i ∧ v.val = row i false)) ∨
  ∃ j, u = e j ∧ XorLine.Adj 4 (x 0 j) v.val

/-- The symmetric outgoing table, retaining the direction of every arc. -/
def freshOld (D : V → V → Prop) (e : Fin 8 → V) (target : Fin 4 → V)
    (u : Fresh) (v : V) : Prop :=
  (Outside e v ∧ ((D (e 7) v ∧ u.val = outputPort 4 (.inl false)) ∨
    ∃ i, v = target i ∧ u.val = row i true)) ∨
  ∃ j, v = e j ∧ XorLine.Adj 4 u.val (x 0 j)

/-- A flat relation specified solely by original adjacency, sixteen original
endpoint names, and the fixed forty-eight-vertex crossing table. -/
def Adj (D : V → V → Prop) (e : Fin 8 → V) (source target : Fin 4 → V) :
    (V ⊕ Fresh) → (V ⊕ Fresh) → Prop
  | .inl u, .inl v => oldOld D e source target u v
  | .inl u, .inr v => oldFresh D e source u v
  | .inr u, .inl v => freshOld D e target u v
  | .inr u, .inr v => XorLine.Adj 4 u.val v.val

instance (D : V → V → Prop) [DecidableRel D] [DecidableEq V]
    (e : Fin 8 → V) (source target : Fin 4 → V) :
    DecidableRel (Adj D e source target) := by
  rintro (u | u) (v | v) <;>
    dsimp [Adj, oldOld, oldFresh, freshOld, Outside] <;> infer_instance

variable (D : V → V → Prop) (e : Fin 8 → V) (source target : Fin 4 → V)
variable (he : Function.Injective e)

@[simp] theorem outside_oldOld (u v : V) (hu : Outside e u) (hv : Outside e v) :
    Adj D e source target (.inl u) (.inl v) ↔
      D u v ∧ ¬∃ i, u = source i ∧ v = target i := by
  simp [Adj, oldOld, hu, hv, fun j => (hu j).symm, fun j => (hv j).symm]

include he in
@[simp] theorem outside_active (u : V) (hu : Outside e u) (j : Fin 8) :
    Adj D e source target (.inl u) (.inl (e j)) ↔ j = 3 ∧ D u (e j) := by
  simp [Adj, oldOld, hu, fun k => (hu k).symm, he.eq_iff]

include he in
@[simp] theorem active_outside (i : Fin 8) (v : V) (hv : Outside e v) :
    Adj D e source target (.inl (e i)) (.inl v) ↔ i = 0 ∧ D (e i) v := by
  simp [Adj, oldOld, hv, fun k => (hv k).symm, he.eq_iff]

include he in
@[simp] theorem active_active (i j : Fin 8) :
    Adj D e source target (.inl (e i)) (.inl (e j)) ↔
      XorLine.Adj 4 (x 0 i) (x 0 j) := by
  simp [Adj, oldOld, he.eq_iff, XorLine.Adj, x]

@[simp] theorem outside_fresh (u : V) (hu : Outside e u) (v : Fresh) :
    Adj D e source target (.inl u) (.inr v) ↔
      (D u (e 4) ∧ v.val = inputPort 4 (.inl false)) ∨
        ∃ i, u = source i ∧ v.val = row i false := by
  simp [Adj, oldFresh, hu, fun j => (hu j).symm]

@[simp] theorem fresh_outside (u : Fresh) (v : V) (hv : Outside e v) :
    Adj D e source target (.inr u) (.inl v) ↔
      (D (e 7) v ∧ u.val = outputPort 4 (.inl false)) ∨
        ∃ i, v = target i ∧ u.val = row i true := by
  simp [Adj, freshOld, hv, fun j => (hv j).symm]

include he in
@[simp] theorem active_fresh (i : Fin 8) (v : Fresh) :
    Adj D e source target (.inl (e i)) (.inr v) ↔
      XorLine.Adj 4 (x 0 i) v.val := by
  simp [Adj, oldFresh, he.eq_iff]

include he in
@[simp] theorem fresh_active (u : Fresh) (j : Fin 8) :
    Adj D e source target (.inr u) (.inl (e j)) ↔
      XorLine.Adj 4 u.val (x 0 j) := by
  simp [Adj, freshOld, he.eq_iff]

include he in
/-- All new internal arcs, including arcs incident with reused names, are
exactly the internal arcs of the tile. -/
theorem tile_tile (u v : XorLine.Vertex 4) :
    Adj D e source target (tileName e u) (tileName e v) ↔ XorLine.Adj 4 u v := by
  obtain ⟨u, rfl⟩ := Numbering.tileEquiv.symm.surjective u
  obtain ⟨v, rfl⟩ := Numbering.tileEquiv.symm.surjective v
  rcases u with i | u <;> rcases v with j | v
  · exact active_active D e source target he i j
  · simpa only [show Numbering.tileEquiv.symm (.inl i) = x 0 i from rfl,
      show Numbering.tileEquiv.symm (.inr v) = v.val from rfl,
      tileName_active, tileName_retained] using active_fresh D e source target he i v
  · simpa only [show Numbering.tileEquiv.symm (.inr u) = u.val from rfl,
      show Numbering.tileEquiv.symm (.inl j) = x 0 j from rfl,
      tileName_active, tileName_retained] using fresh_active D e source target he u j
  · simp only [show Numbering.tileEquiv.symm (.inr u) = u.val from rfl,
      show Numbering.tileEquiv.symm (.inr v) = v.val from rfl,
      tileName_retained, Adj]

/-- The old graph supplies both optional XOR boundary arcs and all four
compulsory bundle boundaries. -/
def enter (D : V → V → Prop) (e : Fin 8 → V) (source : Fin 4 → V)
    (u : V) : Port 4 → Prop
  | .inl b => D u (e (if b then 3 else 4))
  | .inr i => u = source i

def leave (D : V → V → Prop) (e : Fin 8 → V) (target : Fin 4 → V)
    (v : V) : Port 4 → Prop
  | .inl b => D (e (if b then 0 else 7)) v
  | .inr i => v = target i

theorem enter_ports (u : V) (v : XorLine.Vertex 4) :
    (∃ p, enter D e source u p ∧ v = inputPort 4 p) ↔
      (D u (e 3) ∧ v = x 0 3) ∨
      (D u (e 4) ∧ v = inputPort 4 (.inl false)) ∨
      ∃ i, u = source i ∧ v = row i false := by
  simp only [Sum.exists, Bool.exists_bool, enter, inputPort, Bool.false_eq_true,
    ite_false, ite_true]
  tauto

theorem leave_ports (u : XorLine.Vertex 4) (v : V) :
    (∃ p, leave D e target v p ∧ u = outputPort 4 p) ↔
      (D (e 0) v ∧ u = x 0 0) ∨
      (D (e 7) v ∧ u = outputPort 4 (.inl false)) ∨
      ∃ i, v = target i ∧ u = row i true := by
  simp only [Sum.exists, Bool.exists_bool, leave, outputPort, Bool.false_eq_true,
    ite_false, ite_true]
  tauto

include he in
theorem outside_tile (u : V) (hu : Outside e u) (v : XorLine.Vertex 4) :
    Adj D e source target (.inl u) (tileName e v) ↔
      ∃ p, enter D e source u p ∧ v = inputPort 4 p := by
  obtain ⟨v, rfl⟩ := Numbering.tileEquiv.symm.surjective v
  rcases v with j | v
  · change Adj D e source target (.inl u) (.inl (e j)) ↔ _
    rw [outside_active D e source target he u hu j, enter_ports]
    simp [Numbering.tileEquiv, Numbering.tileOriginal, x, row, inputPort, and_comm]
    rintro rfl
    rfl
  · change Adj D e source target (.inl u) (tileName e v.val) ↔ _
    rw [tileName_retained, outside_fresh D e source target u hu v, enter_ports]
    simp [Numbering.tileEquiv, Numbering.tileOriginal, Ne.symm (SatCrossingHorizontal.retained_ne_zero v 3)]

include he in
theorem tile_outside (u : XorLine.Vertex 4) (v : V) (hv : Outside e v) :
    Adj D e source target (tileName e u) (.inl v) ↔
      ∃ p, leave D e target v p ∧ u = outputPort 4 p := by
  obtain ⟨u, rfl⟩ := Numbering.tileEquiv.symm.surjective u
  rcases u with i | u
  · change Adj D e source target (.inl (e i)) (.inl v) ↔ _
    rw [active_outside D e source target he i v hv, leave_ports]
    simp [Numbering.tileEquiv, Numbering.tileOriginal, x, row, outputPort, and_comm]
    rintro rfl
    rfl
  · change Adj D e source target (tileName e u.val) (.inl v) ↔ _
    rw [tileName_retained, fresh_outside D e source target u v hv, leave_ports]
    simp [Numbering.tileEquiv, Numbering.tileOriginal, Ne.symm (SatCrossingHorizontal.retained_ne_zero u 0)]

/-- Relabelling the old graph commutes with the fixed finite table. -/
theorem relabel {W : Type*} (f : V ≃ W) (u v : V ⊕ Fresh) :
    Adj (fun u v => D (f.symm u) (f.symm v)) (fun j => f (e j))
      (fun i => f (source i)) (fun i => f (target i))
      (Sum.map f id u) (Sum.map f id v) ↔ Adj D e source target u v := by
  rcases u with u | u <;> rcases v with v | v <;>
    simp [Adj, oldOld, oldFresh, freshOld, Outside, f.injective.eq_iff]

end Table

/-- Decode the forty fixed fresh names by division and remainder. -/
def retainedDecode (i : Fin 40) : Fresh :=
  if hi : i.val < 32 then
    ⟨.inl (⟨i.val / 8 + 1, by omega⟩, ⟨i.val % 8, by omega⟩), by
      change (⟨i.val / 8 + 1, _⟩ : Fin 5) ≠ 0
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega⟩
  else
    ⟨.inr (⟨(i.val - 32) / 2, by have := i.isLt; omega⟩,
      decide ((i.val - 32) % 2 = 1)), trivial⟩

theorem retainedDecode_index (v : Fresh) :
    retainedDecode (Numbering.retainedIndex v) = v := by decide +kernel +revert

theorem retainedIndex_decode (i : Fin 40) :
    Numbering.retainedIndex (retainedDecode i) = i := by decide +kernel +revert

/-- Unlike an inverse obtained by choice, this inverse is an explicit finite
arithmetic operation that can be used in executable adjacency functions. -/
def retainedComputableEquiv : Fresh ≃ Fin 40 where
  toFun := Numbering.retainedIndex
  invFun := retainedDecode
  left_inv := retainedDecode_index
  right_inv := retainedIndex_decode

def nameEquiv (N : Nat) : (Fin N ⊕ Fresh) ≃ Fin (N + 40) :=
  (Equiv.sumCongr (Equiv.refl _) retainedComputableEquiv).trans finSumFinEquiv

/-- Integer adjacency evaluates the direct fixed table after decoding the
two names. No inverse of the actual crossing graph is consulted. -/
def integerAdj {N : Nat} (D : Fin N → Fin N → Prop) (e : Fin 8 → Fin N)
    (source target : Fin 4 → Fin N) (u v : Fin (N + 40)) : Prop :=
  Adj D e source target ((nameEquiv N).symm u) ((nameEquiv N).symm v)

instance {N : Nat} (D : Fin N → Fin N → Prop) [DecidableRel D]
    (e : Fin 8 → Fin N) (source target : Fin 4 → Fin N) :
    DecidableRel (integerAdj D e source target) := fun _ _ => inferInstanceAs
      (Decidable (Adj D e source target _ _))

@[simp] theorem integerAdj_names {N : Nat} (D : Fin N → Fin N → Prop)
    (e : Fin 8 → Fin N) (source target : Fin 4 → Fin N) (u v : Fin N ⊕ Fresh) :
    integerAdj D e source target (nameEquiv N u) (nameEquiv N v) ↔
      Adj D e source target u v := by simp [integerAdj]

section Actual
variable {n : Nat} (s : IntervalState n) (a : Fin n) (line height : Nat)
variable (hc : s.Covered line height)

abbrev active : Fin 8 → s.Vertex := s.positioned.registry.xors.embed a
abbrev selectedBundle : Bundle s.adj 4 :=
  s.positioned.registry.bundles (s.select line height hc).val

/-- The adjacency table for the bundle that the actual interval lookup selects. -/
def flatAdj : (s.Vertex ⊕ Fresh) → (s.Vertex ⊕ Fresh) → Prop :=
  Adj s.adj (active s a) (selectedBundle s line height hc).source
    (selectedBundle s line height hc).target

def survivor (u : s.Vertex) (hu : Outside (active s a) u) :
    (s.cross a line height hc).Vertex :=
  .inl ⟨.inl u, Bundle.old_not_in_sourceMarker _ _ hu⟩

theorem survivor_name (u : s.Vertex) (hu : Outside (active s a) u) :
    Numbering.equiv s a line height hc (survivor s a line height hc u hu) = .inl u := rfl

theorem tile_name (v : XorLine.Vertex 4) :
    Numbering.equiv s a line height hc (.inr v) = tileName (active s a) v := by
  obtain ⟨v,rfl⟩ := Numbering.tileEquiv.symm.surjective v
  rcases v with j | v
  · exact Numbering.equiv_active s a line height hc j
  · change Numbering.equiv s a line height hc (.inr v.val) = tileName (active s a) v.val
    rw [Numbering.equiv_retained, tileName_retained]

theorem actual_enter (u : s.Vertex) (p : Port 4) :
    Subdivision.Adj s.adj (selectedBundle s line height hc).source
      (selectedBundle s line height hc).target (.inl u)
      (sourceMarker (active s a) (Source.inputPort 4 p)) ↔
      enter s.adj (active s a) (selectedBundle s line height hc).source u p := by
  cases p with
  | inl b =>
    cases b <;>
      change (s.adj u _ ∧ ¬∃ i, u = _ ∧ active s a _ = _) ↔ s.adj u _
    all_goals
      constructor
      · exact And.left
      · intro h
        refine ⟨h,?_⟩
        rintro ⟨i,_,hi⟩
        exact s.positioned.registry.xor_ne_target a (s.select line height hc).val i _ hi
  | inr i => simp [Subdivision.Adj, sourceMarker, Source.inputPort, enter]

theorem actual_leave (p : Port 4) (v : s.Vertex) :
    Subdivision.Adj s.adj (selectedBundle s line height hc).source
      (selectedBundle s line height hc).target
      (sourceMarker (active s a) (Source.outputPort 4 p)) (.inl v) ↔
      leave s.adj (active s a) (selectedBundle s line height hc).target v p := by
  cases p with
  | inl b =>
    cases b <;>
      change (s.adj _ v ∧ ¬∃ i, active s a _ = _ ∧ v = _) ↔ s.adj _ v
    all_goals
      constructor
      · exact And.left
      · intro h
        refine ⟨h,?_⟩
        rintro ⟨i,hi,_⟩
        exact s.positioned.registry.xor_ne_source a (s.select line height hc).val i _ hi
  | inr i => simp [Subdivision.Adj, sourceMarker, Source.outputPort, leave]

theorem survivor_survivor (u v : s.Vertex)
    (hu : Outside (active s a) u) (hv : Outside (active s a) v) :
    (s.cross a line height hc).adj (survivor s a line height hc u hu)
      (survivor s a line height hc v hv) ↔ flatAdj s a line height hc (.inl u) (.inl v) :=
  (outside_oldOld s.adj (active s a) _ _ u v hu hv).symm

theorem survivor_tile (u : s.Vertex) (hu : Outside (active s a) u)
    (v : XorLine.Vertex 4) :
    (s.cross a line height hc).adj (survivor s a line height hc u hu) (.inr v) ↔
      flatAdj s a line height hc (.inl u) (tileName (active s a) v) := by
  change (∃ p, Subdivision.Adj s.adj _ _ (.inl u)
    (sourceMarker (active s a) (Source.inputPort 4 p)) ∧ v = inputPort 4 p) ↔ _
  simp_rw [actual_enter s a line height hc]
  exact (outside_tile s.adj (active s a) _ _
    (s.positioned.registry.xors.embed_injective a) u hu v).symm

theorem tile_survivor (u : XorLine.Vertex 4) (v : s.Vertex)
    (hv : Outside (active s a) v) :
    (s.cross a line height hc).adj (.inr u) (survivor s a line height hc v hv) ↔
      flatAdj s a line height hc (tileName (active s a) u) (.inl v) := by
  change (∃ p, Subdivision.Adj s.adj _ _
    (sourceMarker (active s a) (Source.outputPort 4 p)) (.inl v) ∧ u = outputPort 4 p) ↔ _
  simp_rw [actual_leave s a line height hc]
  exact (tile_outside s.adj (active s a) _ _
    (s.positioned.registry.xors.embed_injective a) u v hv).symm

private theorem outside_decompose
    (o : Marked.Outside (sourceMarker (n := 4) (active s a))) :
    ∃ (u : s.Vertex) (hu : Outside (active s a) u),
      o = ⟨.inl u, Bundle.old_not_in_sourceMarker _ _ hu⟩ := by
  obtain ⟨o,ho⟩ := o
  cases o with
  | inl u =>
    refine ⟨u, ?_, rfl⟩
    intro j hj
    exact ho ⟨.inl j, congrArg Sum.inl hj⟩
  | inr p => exact False.elim (ho ⟨.inr p, rfl⟩)

/-- The flat table is exactly the actual graph produced by interval crossing.
In particular, there are no unstated embedding or boundary assumptions. -/
theorem cross_adj_iff (u v : (s.cross a line height hc).Vertex) :
    (s.cross a line height hc).adj u v ↔
      flatAdj s a line height hc (Numbering.equiv s a line height hc u)
        (Numbering.equiv s a line height hc v) := by
  rcases u with u | u <;> rcases v with v | v
  · obtain ⟨u,hu,rfl⟩ := outside_decompose s a u
    obtain ⟨v,hv,rfl⟩ := outside_decompose s a v
    exact survivor_survivor s a line height hc u v hu hv
  · obtain ⟨u,hu,rfl⟩ := outside_decompose s a u
    rw [tile_name]
    exact survivor_tile s a line height hc u hu v
  · obtain ⟨v,hv,rfl⟩ := outside_decompose s a v
    rw [tile_name]
    exact tile_survivor s a line height hc u v hv
  · rw [tile_name, tile_name]
    exact (tile_tile s.adj (active s a) _ _
      (s.positioned.registry.xors.embed_injective a) u v).symm

/-- The direct adjacency table preserves Hamiltonicity of the original state. -/
theorem hamiltonian_iff : PathCover.Hamiltonian s.adj ↔
    PathCover.Hamiltonian (flatAdj s a line height hc) := by
  exact (s.cross_correct a line height hc).trans
    (PathCover.hamiltonian_relabel_iff _ _ (Numbering.equiv s a line height hc)
      (cross_adj_iff s a line height hc))

section Numbered
variable {N : Nat} (number : s.Vertex ≃ Fin N)

theorem finEquiv_eq (v : (s.cross a line height hc).Vertex) :
    Numbering.finEquiv s number a line height hc v =
      nameEquiv N (Sum.map number id (Numbering.equiv s a line height hc v)) := by
  change finSumFinEquiv ((Equiv.sumCongr number Numbering.retainedEquiv)
    (Numbering.equiv s a line height hc v)) =
    finSumFinEquiv ((Equiv.sumCongr (Equiv.refl _) retainedComputableEquiv)
      (Sum.map number id (Numbering.equiv s a line height hc v)))
  cases Numbering.equiv s a line height hc v <;> rfl

/-- Exact numbered adjacency for the actual refinement, using only the
original numbered graph, the selected bundle endpoints, and the fixed table. -/
theorem numbered_cross_adj_iff (u v : (s.cross a line height hc).Vertex) :
    (s.cross a line height hc).adj u v ↔
      integerAdj (fun i j => s.adj (number.symm i) (number.symm j))
        (fun j => number (active s a j))
        (fun i => number ((selectedBundle s line height hc).source i))
        (fun i => number ((selectedBundle s line height hc).target i))
        (Numbering.finEquiv s number a line height hc u)
        (Numbering.finEquiv s number a line height hc v) := by
  rw [finEquiv_eq, finEquiv_eq, integerAdj_names, relabel]
  exact cross_adj_iff s a line height hc u v

theorem numbered_hamiltonian_iff : PathCover.Hamiltonian s.adj ↔
    PathCover.Hamiltonian
      (integerAdj (fun i j => s.adj (number.symm i) (number.symm j))
        (fun j => number (active s a j))
        (fun i => number ((selectedBundle s line height hc).source i))
        (fun i => number ((selectedBundle s line height hc).target i))) := by
  exact (s.cross_correct a line height hc).trans
    (PathCover.hamiltonian_relabel_iff _ _ (Numbering.finEquiv s number a line height hc)
      (numbered_cross_adj_iff s a line height hc number))

end Numbered
end Actual
end GridHardness.CorrectedSatInterval.NumberedAdjacency
