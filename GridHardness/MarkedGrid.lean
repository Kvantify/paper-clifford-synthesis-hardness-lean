/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridGeometry
public import GridProblems.Source

/-!
# Marked Grid

A total polynomial-cost reduction for grids with a marked degree-two
vertex and an incident edge. The guard checks the marking; it is not an axiom
or a promise silently imposed on the target. `SelectMarking.lean` extends
this reduction to arbitrary grids by selecting and relabelling vertices.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness
open CliffordComplexity CliffordSynthesis
open GridProblems GridProblems.GridCode

def signedDistance : Code (.pair SignedTy SignedTy) .nat :=
  let u := Code.add (.comp .fst .fst) (.comp .snd .snd)
  let v := Code.add (.comp .snd .fst) (.comp .fst .snd)
  Code.add (.comp (.pair u v) .natSub) (.comp (.pair v u) .natSub)

theorem signedDistance_eval (p q : Nat × Nat) :
    signedDistance.eval (p, q) = (integer p - integer q).natAbs := by
  change (p.1 + q.2 - (q.1 + p.2)) + (q.1 + p.2 - (p.1 + q.2)) = _
  unfold integer
  omega

def pointAdjacent : Code (.pair PointTy PointTy) .bool :=
  .comp (.pair
    (Code.add (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) signedDistance)
      (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) signedDistance))
    (.const .nat 1)) .natEq

theorem pointAdjacent_eval (p q : PointTy.denote) :
    pointAdjacent.eval (p, q) = true ↔ IntegerGrid.manhattan (decoded p) (decoded q) = 1 := by
  change decide (signedDistance.eval (p.1, q.1) + signedDistance.eval (p.2, q.2) = 1) = true ↔ _
  rw [decide_eq_true_eq, signedDistance_eval, signedDistance_eval]
  rfl

def startDegree : Code InputTy .nat :=
  .comp (.pair start .fst)
    (.comp (.listMapEnv pointAdjacent) (.comp (.listFilter .id) .listLen))

def markedEdge : Code InputTy .bool :=
  .comp (.pair start (.comp (.pair .fst .snd) Code.listNth))
    (.comp (.listMapEnv pointAdjacent) allCode)

def markedGuard : Code InputTy .bool :=
  Code.and validCode
    (Code.and (.comp (.pair (.const .nat 3) (.comp .fst .listLen)) .natLe)
      (Code.and (.comp (.pair startDegree (.const .nat 2)) .natEq) markedEdge))

theorem startDegree_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (last : Fin (m + 1)) :
    startDegree.eval (input p last) = (IntegerGrid.graph (decoded ∘ p)).degree 0 := by
  change (((List.ofFn p).map (fun q => pointAdjacent.eval (start.eval (input p last), q))).filter id).length = _
  rw [start_eval, ← List.countP_eq_length_filter, List.countP_map]
  have hbool (i : Fin (m + 1)) : pointAdjacent.eval (p 0, p i) =
      decide ((IntegerGrid.graph (decoded ∘ p)).Adj 0 i) := by
    apply Bool.eq_iff_iff.mpr
    simpa [IntegerGrid.graph, Function.comp_def] using pointAdjacent_eval (p 0) (p i)
  have huniv : (List.ofFn (id : Fin (m + 1) → Fin (m + 1))).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_univ, iff_true]
    exact ⟨i, rfl⟩
  have hnodup := List.nodup_ofFn.mpr (Function.injective_id (α := Fin (m + 1)))
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, ← huniv,
    hnodup.card_eq_countP]
  conv_lhs => rw [show List.ofFn p = (List.ofFn id).map p by
    simp only [List.map_ofFn, Function.comp_id]]
  rw [List.countP_map]
  apply List.countP_congr
  intro i _
  simp only [Function.comp_apply, id_eq, hbool]

theorem markedEdge_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (last : Fin (m + 1)) : markedEdge.eval (input p last) = true ↔
      (IntegerGrid.graph (decoded ∘ p)).Adj 0 last := by
  change allCode.eval ((Code.listNth.eval (List.ofFn p, last.val)).map
    (fun q => pointAdjacent.eval (start.eval (input p last), q))) = true ↔ _
  rw [start_eval, listNth_eval (τ := PointTy) (by simpa using last.isLt)]
  simp only [List.getElem_ofFn, List.map_cons, List.map_nil]
  change GridProblems.GridCode.allCode.eval [pointAdjacent.eval (p 0, p last)] = true ↔ _
  rw [GridProblems.GridCode.allCode_eval]
  simp only [List.mem_singleton, forall_eq]
  exact pointAdjacent_eval _ _

theorem markedGuard_eval {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (last : Fin (m + 1)) : markedGuard.eval (input p last) = true ↔
      Function.Injective (decoded ∘ p) ∧ 3 ≤ m + 1 ∧
      (IntegerGrid.graph (decoded ∘ p)).degree 0 = 2 ∧
      (IntegerGrid.graph (decoded ∘ p)).Adj 0 last := by
  change (validCode.eval (input p last) && (decide (3 ≤ (List.ofFn p).length) &&
    (decide (startDegree.eval (input p last) = 2) && markedEdge.eval (input p last)))) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_ofFn, startDegree_eval]
  rw [GridProblems.GridCode.validCode_eval p last, markedEdge_eval p last]

/-- The vertex at position zero is marked, and the endpoint field marks one
of its neighbours. Invalid coordinates, markings and small graphs are rejected. -/
def MARKED_GRID_CYCLE : Problem InputTy.denote := fun x =>
  ∃ (m : Nat) (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)),
    x = input p last ∧ Function.Injective (decoded ∘ p) ∧ 3 ≤ m + 1 ∧
      (IntegerGrid.graph (decoded ∘ p)).degree 0 = 2 ∧
      (IntegerGrid.graph (decoded ∘ p)).Adj 0 last ∧
      ∃ a, ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk a a, w.IsHamiltonianCycle

theorem marked_cycle_guard {x : InputTy.denote} (h : MARKED_GRID_CYCLE x) :
    markedGuard.eval x = true := by
  obtain ⟨m, p, last, rfl, hp, hn, hd, ha, _⟩ := h
  exact (markedGuard_eval p last).mpr ⟨hp, hn, hd, ha⟩

theorem marked_cycle_iff_path {x : InputTy.denote} (h : markedGuard.eval x = true) :
    MARKED_GRID_CYCLE x ↔ GRID_HAMILTONIAN_PATH x := by
  have hv : validCode.eval x = true := (Bool.and_eq_true_iff.mp h).1
  obtain ⟨m, p, last, rfl, _⟩ := (validCode_correct x).mp hv
  obtain ⟨hp, hn, hd, ha⟩ := (markedGuard_eval p last).mp h
  constructor
  · rintro ⟨m', p', last', he, hp', hn', hd', ha', hc⟩
    rw [he, source_input]
    exact ⟨hp', (cycle_iff_path_of_degree_two (by simpa using hn') hd' ha').mp hc⟩
  · intro hx
    refine ⟨m, p, last, rfl, hp, hn, hd, ha, ?_⟩
    exact (cycle_iff_path_of_degree_two (by simpa using hn) hd ha).mpr
      ((source_input p last).mp hx).2

def markedCycleToPath : Code InputTy InputTy :=
  .branch markedGuard .id (.const InputTy ([], 0))

theorem empty_not_grid_path : ¬ GRID_HAMILTONIAN_PATH ([], 0) := by
  rintro ⟨m, p, last, he, _⟩
  have h := congrArg (fun x : InputTy.denote => x.1.length) he
  simp [input] at h

theorem markedCycleToPath_correct (x : InputTy.denote) :
    MARKED_GRID_CYCLE x ↔ GRID_HAMILTONIAN_PATH (markedCycleToPath.eval x) := by
  change MARKED_GRID_CYCLE x ↔ GRID_HAMILTONIAN_PATH (if markedGuard.eval x then x else ([], 0))
  by_cases h : markedGuard.eval x = true
  · rw [ite_eq_left h]
    exact marked_cycle_iff_path h
  · rw [ite_eq_right h]
    exact iff_of_false (fun hx => h (marked_cycle_guard hx)) empty_not_grid_path

/-- Fully proved in the same cost model as the SAT prefix and synthesis reductions. -/
def certifiedMarkedCycleToPath : CertifiedReduction MARKED_GRID_CYCLE GRID_HAMILTONIAN_PATH where
  code := markedCycleToPath
  correct := markedCycleToPath_correct

end GridHardness
