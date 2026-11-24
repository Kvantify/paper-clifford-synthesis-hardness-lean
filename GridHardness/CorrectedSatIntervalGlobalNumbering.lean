/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRowNumbering
public import GridHardness.CorrectedSatIntervalGraph
public import GridHardness.PlanarSatCodeAssembly
public import Mathlib.Data.List.NodupEquivFin

/-!
# Corrected SAT Interval Global Numbering

Explicit vertex names for the entire two-sided insertion sweep.
The equivalence follows the actual crossing recursion: original names are
reused, and each crossing appends forty names in execution order. No
cardinality-based enumeration of the final graph is used.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.CorrectedSatInterval.GlobalNumbering
open XorLineRegistry XorLineSchedule XorLine

/-- Replacing an XOR preserves its eight names by giving them to the refreshed
section zero. Vertices outside that XOR have their usual survivor image. -/
noncomputable def crossLift {n : Nat} (s : IntervalState n) (a : Fin n)
    (line height : Nat) (hc : s.Covered line height) :
    s.Vertex → (s.cross a line height hc).Vertex :=
  fun v => (Numbering.equiv s a line height hc).symm (.inl v)

theorem crossLift_survivor {n : Nat} (s : IntervalState n) (a : Fin n)
    (line height : Nat) (hc : s.Covered line height) (o : Boundary.Outside s a) :
    crossLift s a line height hc o.val =
      (Boundary.transport s a line height hc o).val := by
  apply (Numbering.equiv s a line height hc).injective
  rw [crossLift, Equiv.apply_symm_apply]
  rfl

theorem crossLift_current_xor {n : Nat} (s : IntervalState n) (a : Fin n)
    (line height : Nat) (hc : s.Covered line height) (k : Fin 8) :
    crossLift s a line height hc (s.positioned.registry.xors.embed a k) =
      (s.cross a line height hc).positioned.registry.xors.embed a k := by
  apply (Numbering.equiv s a line height hc).injective
  rw [crossLift, Equiv.apply_symm_apply, Numbering.equiv_current_xor]

theorem crossLift_other_xor {n : Nat} (s : IntervalState n) (a b : Fin n)
    (hba : b ≠ a) (line height : Nat) (hc : s.Covered line height) (k : Fin 8) :
    crossLift s a line height hc (s.positioned.registry.xors.embed b k) =
      (s.cross a line height hc).positioned.registry.xors.embed b k := by
  apply (Numbering.equiv s a line height hc).injective
  rw [crossLift, Equiv.apply_symm_apply, Numbering.equiv_other_xor _ _ _ _ _ _ hba]

theorem crossLift_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (line height : Nat) (hc : s.Covered line height) (v : s.Vertex) :
    (Numbering.finEquiv s number a line height hc (crossLift s a line height hc v)).val =
      (number v).val := by
  change (finSumFinEquiv ((Equiv.sumCongr number Numbering.retainedEquiv)
    ((Numbering.equiv s a line height hc)
      ((Numbering.equiv s a line height hc).symm (.inl v))))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Carry every old name through a row, including the active XOR names. -/
noncomputable def rowLift {n : Nat} (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈ rs, s.Covered i height) :
    s.Vertex → (s.crossRequests a height rs hn hc).Vertex :=
  match rs with
  | [] => id
  | i::is => fun v =>
    rowLift (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) v)

theorem rowLift_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height : Nat) (rs : List Nat) (hn : rs.Nodup)
    (hc : ∀ i ∈ rs, s.Covered i height) (v : s.Vertex) :
    (RowNumbering.equiv s number a height rs hn hc
      (rowLift s a height rs hn hc v)).val = (number v).val := by
  induction rs generalizing N s with
  | nil => rfl
  | cons i is ih =>
    change (RowNumbering.equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (rowLift (s.cross a i height (hc i (by simp))) a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
        (crossLift s a i height (hc i (by simp)) v))).val = _
    rw [ih, crossLift_names]

theorem rowLift_outside {n : Nat} (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈ rs, s.Covered i height)
    (o : Boundary.Outside s a) :
    rowLift s a height rs hn hc o.val =
      (Boundary.carryRequests s a height rs hn hc o).val := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    change rowLift (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) o.val) = _
    rw [crossLift_survivor]
    exact ih _ _ _ _

theorem rowLift_current_xor {n : Nat} (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈ rs, s.Covered i height) (k : Fin 8) :
    rowLift s a height rs hn hc (s.positioned.registry.xors.embed a k) =
      (s.crossRequests a height rs hn hc).positioned.registry.xors.embed a k := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    change rowLift (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp))
        (s.positioned.registry.xors.embed a k)) = _
    rw [crossLift_current_xor]
    exact ih _ _ _

noncomputable def nextLift {n : Nat} (s : IntervalState (n +1))
    (height : Nat → Nat) (j : Nat) (h : Ready s height j) :
    s.Vertex → (next s height j h).Vertex :=
  rowLift s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered

theorem nextLift_names {n N : Nat} (s : IntervalState (n +1))
    (number : s.Vertex ≃ Fin N) (height : Nat → Nat) (j : Nat) (h : Ready s height j)
    (v : s.Vertex) :
    (RowNumbering.nextEquiv s number height j h (nextLift s height j h v)).val =
      (number v).val :=
  rowLift_names s number 0 (height j) _ _ _ v

/-- Number the actual complete recursion, retaining the numbering of each
intermediate state as the input numbering for the next row. -/
noncomputable def runEquiv (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) : (n j N : Nat) → (s : IntervalState n) →
    (h : Ready s height j) → (s.Vertex ≃ Fin N) →
    (runState height hinj hpos n j s h).Vertex ≃ Fin (N+40*moveCount height n j)
  | 0, _, _, _, _, number => number.trans (finCongr (by simp [moveCount]))
  | n+1, j, N, s, h, number =>
    (runEquiv height hinj hpos n (j+1) (N+40*(requests height j).length)
      (next s height j h) (next_ready s height hinj hpos j h)
      (RowNumbering.nextEquiv s number height j h)).trans
        (finCongr (by simp only [moveCount]; omega))

/-- Structural transport of initial names throughout the complete sweep.
This follows the same crossing and retirement recursion as the graph. -/
noncomputable def runLift (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) : (n j : Nat) → (s : IntervalState n) →
    (h : Ready s height j) → s.Vertex → (runState height hinj hpos n j s h).Vertex
  | 0, _, _, _, v => v
  | n+1, j, s, h, v =>
    runLift height hinj hpos n (j+1) (next s height j h)
      (next_ready s height hinj hpos j h) (nextLift s height j h v)

theorem runLift_names (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ (j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N) (v : s.Vertex),
    (runEquiv height hinj hpos n j N s h number
      (runLift height hinj hpos n j s h v)).val = (number v).val := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro j N s h number v
    change (runEquiv height hinj hpos n (j+1) (N+40*(requests height j).length)
      (next s height j h) (next_ready s height hinj hpos j h)
      (RowNumbering.nextEquiv s number height j h)
      (runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) (nextLift s height j h v))).val = _
    rw [ih, nextLift_names]

theorem runLift_injective (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N) :
    Function.Injective (runLift height hinj hpos n j s h) := by
  intro u v he
  apply number.injective
  apply Fin.ext
  have hn := congrArg (fun z => (runEquiv height hinj hpos n j N s h number z).val) he
  simpa only [runLift_names] using hn

/-- The retained vertex allocated by a specified crossing of one row,
transported through the later crossings of that row. -/
noncomputable def rowFresh {n : Nat} (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈ rs, s.Covered i height) :
    Fin rs.length → SatCrossingHorizontal.RetainedVertex →
      (s.crossRequests a height rs hn hc).Vertex :=
  match rs with
  | [] => fun t => Fin.elim0 t
  | i::is => fun t v =>
    if ht : t.val = 0 then
      rowLift (s.cross a i height (hc i (by simp))) a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
        (.inr v.val)
    else
      rowFresh (s.cross a i height (hc i (by simp))) a height is
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
        ⟨t.val-1, by have := t.isLt; simp only [List.length_cons] at this; omega⟩ v

theorem rowFresh_names {n N : Nat} (s : IntervalState n) (number : s.Vertex ≃ Fin N)
    (a : Fin n) (height : Nat) (rs : List Nat) (hn : rs.Nodup)
    (hc : ∀ i ∈ rs, s.Covered i height) (t : Fin rs.length)
    (v : SatCrossingHorizontal.RetainedVertex) :
    (RowNumbering.equiv s number a height rs hn hc
      (rowFresh s a height rs hn hc t v)).val =
      N+40*t.val+(Numbering.retainedIndex v).val := by
  induction rs generalizing N s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    change (RowNumbering.equiv (s.cross a i height (hc i (by simp)))
      (Numbering.finEquiv s number a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (rowFresh s a height (i::is) hn hc t v)).val = _
    by_cases ht : t.val = 0
    · simp only [rowFresh, dite_eq_left ht]
      rw [rowLift_names, Numbering.finEquiv_retained]
      simp [ht]
    · simp only [rowFresh, dite_eq_right ht]
      rw [ih]
      dsimp only
      omega

/-- A fresh vertex is identified by its chronological crossing index and
its fixed local index. This follows its actual allocation, then carries it
through every later row. -/
noncomputable def runFresh (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) : (n j : Nat) → (s : IntervalState n) →
    (h : Ready s height j) → Fin (moveCount height n j) →
    SatCrossingHorizontal.RetainedVertex → (runState height hinj hpos n j s h).Vertex
  | 0, _, _, _, t, _ => Fin.elim0 t
  | n+1, j, s, h, t, v =>
    if ht : t.val < (requests height j).length then
      runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)
        (rowFresh s 0 (height j) (requests height j) (requests_nodup height j)
          h.requests_covered ⟨t.val,ht⟩ v)
    else
      runFresh height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)
        ⟨t.val-(requests height j).length, by
          have := t.isLt; simp only [moveCount] at this; omega⟩ v

theorem runFresh_names (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ (j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N)
    (t : Fin (moveCount height n j)) (v : SatCrossingHorizontal.RetainedVertex),
    (runEquiv height hinj hpos n j N s h number
      (runFresh height hinj hpos n j s h t v)).val =
      N+40*t.val+(Numbering.retainedIndex v).val := by
  induction n with
  | zero => intro j N s h number t; exact Fin.elim0 t
  | succ n ih =>
    intro j N s h number t v
    change (runEquiv height hinj hpos n (j+1) (N+40*(requests height j).length)
      (next s height j h) (next_ready s height hinj hpos j h)
      (RowNumbering.nextEquiv s number height j h)
      (runFresh height hinj hpos (n+1) j s h t v)).val = _
    by_cases ht : t.val < (requests height j).length
    · simp only [runFresh, dite_eq_left ht]
      rw [runLift_names]
      exact rowFresh_names s number 0 (height j) _ _ _ _ v
    · simp only [runFresh, dite_eq_right ht]
      rw [ih]
      dsimp only
      omega

/-- Consecutive arithmetic names for original vertices and chronological
forty-vertex blocks. -/
noncomputable def nameEquiv {V : Type*} {N : Nat} (number : V ≃ Fin N) (k : Nat) :
    V ⊕ (Fin k × SatCrossingHorizontal.RetainedVertex) ≃ Fin (N+40*k) :=
  ((Equiv.sumCongr number
    ((Equiv.prodCongr (Equiv.refl (Fin k)) Numbering.retainedEquiv).trans finProdFinEquiv)).trans
      finSumFinEquiv).trans (finCongr (by omega))

theorem nameEquiv_old {V : Type*} {N : Nat} (number : V ≃ Fin N) (k : Nat) (v : V) :
    (nameEquiv number k (.inl v)).val = (number v).val := rfl

theorem nameEquiv_fresh {V : Type*} {N : Nat} (number : V ≃ Fin N) (k : Nat)
    (t : Fin k) (v : SatCrossingHorizontal.RetainedVertex) :
    (nameEquiv number k (.inr (t,v))).val =
      N+40*t.val+(Numbering.retainedIndex v).val := by
  change N+((Numbering.retainedIndex v).val+40*t.val) = _
  omega

/-- Exact provenance decomposition of the final vertex type. In particular,
the original vertices and the forty retained vertices of each crossing
exhaust the result, with no identifications or leftover unnamed vertices. -/
noncomputable def decomposition (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N) :
    (runState height hinj hpos n j s h).Vertex ≃
      s.Vertex ⊕ (Fin (moveCount height n j) × SatCrossingHorizontal.RetainedVertex) :=
  (runEquiv height hinj hpos n j N s h number).trans
    (nameEquiv number (moveCount height n j)).symm

theorem decomposition_old (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N) (v : s.Vertex) :
    decomposition height hinj hpos n j N s h number
      (runLift height hinj hpos n j s h v) = .inl v := by
  apply (nameEquiv number (moveCount height n j)).injective
  apply Fin.ext
  change ((nameEquiv number (moveCount height n j))
    ((nameEquiv number (moveCount height n j)).symm
      (runEquiv height hinj hpos n j N s h number
        (runLift height hinj hpos n j s h v)))).val = _
  rw [Equiv.apply_symm_apply, runLift_names, nameEquiv_old]

theorem decomposition_fresh (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n j N : Nat) (s : IntervalState n)
    (h : Ready s height j) (number : s.Vertex ≃ Fin N)
    (t : Fin (moveCount height n j)) (v : SatCrossingHorizontal.RetainedVertex) :
    decomposition height hinj hpos n j N s h number
      (runFresh height hinj hpos n j s h t v) = .inr (t,v) := by
  apply (nameEquiv number (moveCount height n j)).injective
  apply Fin.ext
  change ((nameEquiv number (moveCount height n j))
    ((nameEquiv number (moveCount height n j)).symm
      (runEquiv height hinj hpos n j N s h number
        (runFresh height hinj hpos n j s h t v)))).val = _
  rw [Equiv.apply_symm_apply, runFresh_names, nameEquiv_fresh]

/-- Crossing indices identify the actual cells in chronological trace order. -/
noncomputable def traceEquiv (height : Nat → Nat) (n j : Nat) :
    Fin (moveCount height n j) ≃ {p : Nat × Nat // p ∈ trace height n j} :=
  (finCongr (trace_length height n j).symm).trans
    (List.Nodup.getEquiv (trace height n j) (trace_nodup height n j))

theorem traceEquiv_val (height : Nat → Nat) (n j : Nat)
    (t : Fin (moveCount height n j)) :
    (traceEquiv height n j t).val =
      (trace height n j)[t.val]'(by rw [trace_length]; exact t.isLt) := rfl

/-- The initial compiler's explicit consecutive blocks: sentinel, variable,
clause, and occurrence-XOR vertices. -/
noncomputable def initialEquiv {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    (initialState φ).Vertex ≃ Fin (3+2*n+36*m) :=
  (PlanarSatCode.numbering n m).equivFin.trans
    (finCongr (by rw [PlanarSatCode.numbering_size]; omega))

theorem initialEquiv_val {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (v : PlanarSatAssembly.Vertex n m) :
    (initialEquiv φ v).val = (PlanarSatCode.numbering n m).num v := rfl

noncomputable def formulaEquiv {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    (graph φ).Vertex ≃ Fin (3+2*n+36*m+40*moveCount (formulaHeight φ) (3*m) 0) :=
  runEquiv (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (3*m) 0 (3+2*n+36*m) (initialState φ) (initial_ready φ) (initialEquiv φ)

noncomputable def formulaLift {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    PlanarSatAssembly.Vertex n m → (graph φ).Vertex :=
  runLift (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (3*m) 0 (initialState φ) (initial_ready φ)

theorem formulaLift_names {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (v : PlanarSatAssembly.Vertex n m) :
    (formulaEquiv φ (formulaLift φ v)).val = (PlanarSatCode.numbering n m).num v :=
  runLift_names (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (3*m) 0 (3+2*n+36*m) (initialState φ) (initial_ready φ) (initialEquiv φ) v

/-- Number the vertices of the encoded graph using its crossing count. -/
noncomputable def actualEquiv (x : CliffordComplexity.SatTy.denote) :
    (actualGraph x).Vertex ≃ Fin
      (3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+
        40*(SatCrossingCode.crossings.eval x).length) :=
  (formulaEquiv (finiteFormula x)).trans (finCongr (by rw [actual_move_count]))

theorem actual_original_names (x : CliffordComplexity.SatTy.denote)
    (v : PlanarSatAssembly.Vertex ((CliffordComplexity.vsOf x).length +1) x.length) :
    (actualEquiv x (formulaLift (finiteFormula x) v)).val =
      (PlanarSatCode.numbering ((CliffordComplexity.vsOf x).length+1) x.length).num v := by
  simp only [actualEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  exact formulaLift_names (finiteFormula x) v

/-- The same actual crossing cells, with their chronological position supplied
by the insertion trace rather than by the catalogue's enumeration order. -/
noncomputable def catalogueEquiv (x : CliffordComplexity.SatTy.denote) :
    Fin (moveCount (formulaHeight (finiteFormula x)) (3*x.length) 0) ≃
      {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x} :=
  (traceEquiv (formulaHeight (finiteFormula x)) (3*x.length) 0).trans {
    toFun := fun p => ⟨p.val, (covers_catalogue x p.val).mp p.property⟩
    invFun := fun p => ⟨p.val, (covers_catalogue x p.val).mpr p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem catalogueEquiv_symm_val (x : CliffordComplexity.SatTy.denote)
    (p : {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x}) :
    ((catalogueEquiv x).symm p).val =
      (trace (formulaHeight (finiteFormula x)) (3*x.length) 0).idxOf p.val := by
  have hh := congrArg Subtype.val ((catalogueEquiv x).apply_symm_apply p)
  change (traceEquiv (formulaHeight (finiteFormula x)) (3*x.length) 0
    ((catalogueEquiv x).symm p)).val = p.val at hh
  rw [traceEquiv_val] at hh
  rw [← hh]
  exact ((trace_nodup (formulaHeight (finiteFormula x)) (3*x.length) 0).idxOf_getElem
    ((catalogueEquiv x).symm p).val (by rw [trace_length]; exact
      ((catalogueEquiv x).symm p).isLt)).symm

/-- Every final graph vertex is uniquely either an original SAT vertex
(with refreshed XOR sections counted under their original names) or one
of the forty retained vertices at an actual catalogue cell. -/
noncomputable def actualDecomposition (x : CliffordComplexity.SatTy.denote) :
    (actualGraph x).Vertex ≃
      PlanarSatAssembly.Vertex ((CliffordComplexity.vsOf x).length+1) x.length ⊕
        ({p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x} ×
          SatCrossingHorizontal.RetainedVertex) :=
  (decomposition (formulaHeight (finiteFormula x)) (formulaHeight_injective (finiteFormula x))
    (formulaHeight_pos (finiteFormula x)) (3*x.length) 0
    (3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length)
    (initialState (finiteFormula x)) (initial_ready (finiteFormula x))
    (initialEquiv (finiteFormula x))).trans
      (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr (catalogueEquiv x) (Equiv.refl _)))

noncomputable def actualFresh (x : CliffordComplexity.SatTy.denote)
    (p : {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x})
    (v : SatCrossingHorizontal.RetainedVertex) : (actualGraph x).Vertex :=
  runFresh (formulaHeight (finiteFormula x)) (formulaHeight_injective (finiteFormula x))
    (formulaHeight_pos (finiteFormula x)) (3*x.length) 0
    (initialState (finiteFormula x)) (initial_ready (finiteFormula x))
    ((catalogueEquiv x).symm p) v

theorem actualDecomposition_old (x : CliffordComplexity.SatTy.denote)
    (v : PlanarSatAssembly.Vertex ((CliffordComplexity.vsOf x).length +1) x.length) :
    actualDecomposition x (formulaLift (finiteFormula x) v) = .inl v := by
  change (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (catalogueEquiv x) (Equiv.refl _)))
    (decomposition _ _ _ _ _ _ _ _ _
      (runLift _ _ _ _ _ (initialState (finiteFormula x)) _ v)) = _
  rw [decomposition_old]
  rfl

theorem actualDecomposition_fresh (x : CliffordComplexity.SatTy.denote)
    (p : {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x})
    (v : SatCrossingHorizontal.RetainedVertex) :
    actualDecomposition x (actualFresh x p v) = .inr (p,v) := by
  change (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (catalogueEquiv x) (Equiv.refl _)))
    (decomposition _ _ _ _ _ _ _ _ _ (runFresh _ _ _ _ _ _ _ ((catalogueEquiv x).symm p) v)) = _
  rw [decomposition_fresh]
  change Sum.inr ((catalogueEquiv x) ((catalogueEquiv x).symm p),v) = _
  rw [Equiv.apply_symm_apply]

theorem actual_fresh_names (x : CliffordComplexity.SatTy.denote)
    (p : {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x})
    (v : SatCrossingHorizontal.RetainedVertex) :
    (actualEquiv x (actualFresh x p v)).val =
      3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+
        40*(trace (formulaHeight (finiteFormula x)) (3*x.length) 0).idxOf p.val+
          (Numbering.retainedIndex v).val := by
  simp only [actualEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  change (runEquiv _ _ _ _ _ _ _ _ _ (runFresh _ _ _ _ _ _ _ _ _)).val = _
  rw [runFresh_names, catalogueEquiv_symm_val]

theorem actual_vertex_cases (x : CliffordComplexity.SatTy.denote)
    (v : (actualGraph x).Vertex) :
    (∃ u, formulaLift (finiteFormula x) u = v) ∨
      ∃ p r, actualFresh x p r = v := by
  cases h : actualDecomposition x v with
  | inl u =>
    refine Or.inl ⟨u, (actualDecomposition x).injective ?_⟩
    rw [actualDecomposition_old, h]
  | inr p =>
    refine Or.inr ⟨p.1,p.2, (actualDecomposition x).injective ?_⟩
    rw [actualDecomposition_fresh, h]

theorem actual_fresh_injective (x : CliffordComplexity.SatTy.denote) :
    Function.Injective (fun p :
      {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x} ×
        SatCrossingHorizontal.RetainedVertex => actualFresh x p.1 p.2) := by
  intro p q he
  have hn := congrArg (actualDecomposition x) he
  exact Sum.inr.inj ((actualDecomposition_fresh x p.1 p.2).symm.trans
    (hn.trans (actualDecomposition_fresh x q.1 q.2)))

theorem actual_old_ne_fresh (x : CliffordComplexity.SatTy.denote)
    (u : PlanarSatAssembly.Vertex ((CliffordComplexity.vsOf x).length +1) x.length)
    (p : {p : Nat × Nat // p ∈ SatCrossingCode.crossings.eval x})
    (v : SatCrossingHorizontal.RetainedVertex) :
    formulaLift (finiteFormula x) u ≠ actualFresh x p v := by
  intro he
  have hn := congrArg (actualDecomposition x) he
  rw [actualDecomposition_old, actualDecomposition_fresh] at hn
  cases hn

end GridHardness.CorrectedSatInterval.GlobalNumbering
