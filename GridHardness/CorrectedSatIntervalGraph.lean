/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalCatalogue
public import GridHardness.CorrectedSatScheduleGraph

/-!
# Corrected SAT Interval Graph

The whole SAT graph produced by the two-sided insertion sweep. This is an
actual finite graph construction with internally proved interval coverage.
Its planar drawing and its certified encoded implementation remain separate
obligations.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval
open PlanarSatAssembly XorLineRegistry XorLineSchedule

def initialState {n m : Nat} (φ : Formula n m) : IntervalState (3*m) where
  Vertex := PlanarSatAssembly.Vertex n m
  finite := inferInstance
  adj := Adj φ
  BundleId := Empty
  decEq := inferInstance
  positioned := {
    registry := initial (CorrectedSatSchedule.occurrenceFamily φ)
    segments := Empty.elim
    unique := by intro _ _ b; exact b.elim }
  enum := []
  complete := fun b => b.elim

theorem initial_ready {n m : Nat} (φ : Formula n m) :
    Ready (initialState φ) (formulaHeight φ) 0 where
  bound := fun b => b.elim
  covered := by intro i k hi; omega

def graph {n m : Nat} (φ : Formula n m) : FiniteGraph :=
  run (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (3*m) 0 (initialState φ) (initial_ready φ)

def finalState {n m : Nat} (φ : Formula n m) : IntervalState 0 :=
  runState (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (3*m) 0 (initialState φ) (initial_ready φ)

theorem finalState_graph {n m : Nat} (φ : Formula n m) :
    (finalState φ).toFiniteGraph = graph φ := rfl

theorem final_enum_length_le {n m : Nat} (φ : Formula n m) :
    (finalState φ).enum.length ≤ 3*m+2*moveCount (formulaHeight φ) (3*m) 0 := by
  have h := runState_enum_length_le (formulaHeight φ) (formulaHeight_injective φ)
    (formulaHeight_pos φ) (3*m) 0 (initialState φ) (initial_ready φ)
  change (finalState φ).enum.length ≤ 0+3*m+2*moveCount (formulaHeight φ) (3*m) 0 at h
  simpa only [Nat.zero_add] using h

theorem correct {n m : Nat} (φ : Formula n m) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ).adj :=
  (PlanarSatReduction.correct φ).trans (run_correct (formulaHeight φ)
    (formulaHeight_injective φ) (formulaHeight_pos φ) (3*m) 0
    (initialState φ) (initial_ready φ))

theorem vertex_count {n m : Nat} (φ : Formula n m) :
    Nat.card (graph φ).Vertex = 3+2*n+36*m+40*moveCount (formulaHeight φ) (3*m) 0 := by
  rw [graph, run_vertex_count]
  change Nat.card (PlanarSatAssembly.Vertex n m)+_=_
  rw [Nat.card_eq_fintype_card, PlanarSatAssembly.vertex_card]

theorem vertex_bound {n m : Nat} (φ : Formula n m) :
    Nat.card (graph φ).Vertex ≤ 3+2*n+36*m+360*m*m := by
  rw [vertex_count]
  have h := moveCount_le (formulaHeight φ) (3*m) 0
  nlinarith

def actualGraph (x : CliffordComplexity.SatTy.denote) : FiniteGraph := graph (finiteFormula x)

theorem actual_vertex_count (x : CliffordComplexity.SatTy.denote) :
    Nat.card (actualGraph x).Vertex =
      3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+
        40*(SatCrossingCode.crossings.eval x).length := by
  rw [actualGraph, vertex_count, actual_move_count]

theorem actual_vertex_bound (x : CliffordComplexity.SatTy.denote) :
    Nat.card (actualGraph x).Vertex ≤
      3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+360*x.length*x.length :=
  vertex_bound (finiteFormula x)

theorem actual_enum_length_le (x : CliffordComplexity.SatTy.denote) :
    (finalState (finiteFormula x)).enum.length ≤
      3*x.length+2*(SatCrossingCode.crossings.eval x).length := by
  calc
    _ ≤ 3*x.length+2*moveCount (formulaHeight (finiteFormula x)) (3*x.length) 0 :=
      final_enum_length_le (finiteFormula x)
    _ = _ := by rw [actual_move_count]

theorem actual_enum_polynomial_bound (x : CliffordComplexity.SatTy.denote) :
    (finalState (finiteFormula x)).enum.length ≤ 3*x.length+18*x.length*x.length := by
  apply (final_enum_length_le (finiteFormula x)).trans
  have hm := moveCount_le (formulaHeight (finiteFormula x)) (3*x.length) 0
  nlinarith

theorem actual_positive_correct (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) (hp : ∀ c ∈x, ∀ v ∈c, v.2 =true) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      PathCover.Hamiltonian (actualGraph x).adj :=
  (finiteFormula_correct x hw hp).symm.trans (correct (finiteFormula x))

def positiveGraph (x : CliffordComplexity.SatTy.denote) : FiniteGraph :=
  if CorrectedSatSchedule.validSyntax x then actualGraph x
  else CorrectedSatSchedule.invalidGraph

theorem positive_correct (x : CliffordComplexity.SatTy.denote) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      PathCover.Hamiltonian (positiveGraph x).adj := by
  by_cases hv : CorrectedSatSchedule.validSyntax x
  · rw [positiveGraph, ite_eq_left hv]
    exact actual_positive_correct x hv.1 hv.2
  · rw [positiveGraph, ite_eq_right hv]
    constructor
    · intro h
      obtain ⟨hp,hw,_⟩ := (CliffordComplexity.Concrete.monotoneOneInThree3Sat_iff x).mp h
      exact False.elim (hv ⟨hw,hp⟩)
    · rintro ⟨step,ho,ha⟩
      exact False.elim (ha (0 : Fin 2))

end GridHardness.CorrectedSatInterval
