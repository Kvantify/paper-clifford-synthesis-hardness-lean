/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatScheduleCatalogue
public import GridHardness.CorrectedSatGraph
public import GridHardness.SatCrossingCode

/-!
# Corrected SAT Schedule Graph

Execute a two-sided insertion schedule for SAT occurrence crossings.
This constructs the finite graph, exact crossing coverage, Hamiltonian
equivalence and a polynomial vertex bound. These are semantic graph results;
the geometric and executable SAT construction uses the interval sweep in
`CorrectedSatInterval*` and the compiler in `SatCompiledGridReduction`.
-/

@[expose] public section

namespace GridHardness.CorrectedSatSchedule
open PlanarSatAssembly XorLineSchedule XorLineRegistry

/-- Label pending XORs by their exact variable-side occurrence order. -/
def occurrenceFamily {n m : Nat} (φ : Formula n m) : Family (Adj φ) (Fin (3*m)) where
  embed := fun i => PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm i)
  injective := by
    rintro ⟨i,j⟩ ⟨k,l⟩ h
    have he : ((SatWireLayout.variableRank φ).symm i,j)=
        ((SatWireLayout.variableRank φ).symm k,l) := (CorrectedSatGraph.family φ).injective h
    have hp := Prod.mk.inj he
    exact Prod.ext ((SatWireLayout.variableRank φ).symm.injective hp.1) hp.2
  isolated := fun i => (CorrectedSatGraph.family φ).isolated _

def initialState {n m : Nat} (φ : Formula n m) : State (Fin (3*m)) Empty where
  Vertex := PlanarSatAssembly.Vertex n m
  finite := inferInstance
  adj := Adj φ
  registry := XorLineRegistry.initial (occurrenceFamily φ)

/-- An actual whole-SAT graph, executing the finite catalogue plan. -/
def graph {n m : Nat} (φ : Formula n m) (cells : List (Nat ×Nat)) : FiniteGraph :=
  (plan (3*m) cells).run (initialState φ)

theorem correct {n m : Nat} (φ : Formula n m) (cells : List (Nat ×Nat)) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ cells).adj :=
  (PlanarSatReduction.correct φ).trans ((plan (3*m) cells).run_correct (initialState φ))

theorem vertex_count {n m : Nat} (φ : Formula n m) (cells : List (Nat ×Nat)) :
    Nat.card (graph φ cells).Vertex=3+2*n+36*m+40*(plan (3*m) cells).length := by
  rw [graph,Program.run_vertex_count]
  change Nat.card (PlanarSatAssembly.Vertex n m)+_=_
  rw [Nat.card_eq_fintype_card,PlanarSatAssembly.vertex_card]

theorem vertex_bound {n m : Nat} (φ : Formula n m) (cells : List (Nat ×Nat)) :
    Nat.card (graph φ cells).Vertex≤3+2*n+36*m+360*m*m := by
  rw [vertex_count]
  have h := plan_length_le (3*m) cells
  nlinarith

/-- The crossing catalogue already emitted by the finite-list SAT compiler. -/
def actualGraph (x : CliffordComplexity.SatTy.denote) : FiniteGraph :=
  graph (finiteFormula x) (SatCrossingCode.crossings.eval x)

theorem covers_crossings (x : CliffordComplexity.SatTy.denote) (p : Nat ×Nat) :
    p∈(plan (3*x.length) (SatCrossingCode.crossings.eval x)).trace Fin.val Empty.elim ↔
      p∈SatCrossingCode.crossings.eval x := by
  rw [mem_plan_trace]
  constructor
  · exact fun h => h.1
  · intro hp
    obtain ⟨hi,hj,hh,_⟩ := (SatCrossingCode.mem_crossings x p.1 p.2).mp hp
    exact ⟨hp,hh,hj⟩

/-- Each original crossing is executed exactly once; only execution order changes. -/
theorem trace_perm_catalogue (x : CliffordComplexity.SatTy.denote) :
    ((plan (3*x.length) (SatCrossingCode.crossings.eval x)).trace Fin.val Empty.elim).Perm
      (SatCrossingCode.crossings.eval x) :=
  (List.perm_ext_iff_of_nodup (plan_trace_nodup _ _) (SatCrossingCode.crossings_nodup x)).mpr
    (covers_crossings x)

theorem actual_move_count (x : CliffordComplexity.SatTy.denote) :
    (plan (3*x.length) (SatCrossingCode.crossings.eval x)).length=
      (SatCrossingCode.crossings.eval x).length := by
  rw [← Program.trace_length _ Fin.val Empty.elim]
  exact (trace_perm_catalogue x).length_eq

theorem actual_vertex_count (x : CliffordComplexity.SatTy.denote) :
    Nat.card (actualGraph x).Vertex=
      3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+
        40*(SatCrossingCode.crossings.eval x).length := by
  rw [actualGraph,vertex_count,actual_move_count]

theorem actual_vertex_bound (x : CliffordComplexity.SatTy.denote) :
    Nat.card (actualGraph x).Vertex≤
      3+2*((CliffordComplexity.vsOf x).length+1)+36*x.length+360*x.length*x.length :=
  vertex_bound (finiteFormula x) _

/-- Exact coverage of geometric occurrence inversions, using the original
catalogue's proved interpretation rather than an assumed crossing schedule. -/
theorem covers_inversion (x : CliffordComplexity.SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈(plan (3*x.length) (SatCrossingCode.crossings.eval x)).trace Fin.val Empty.elim ↔
      i<j ∧ SatWireLayout.permutation (finiteFormula x) j<
        SatWireLayout.permutation (finiteFormula x) i := by
  rw [covers_crossings,SatCrossingCode.crossing_cell_iff]

theorem actual_positive_correct (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) (hp : ∀ c ∈x, ∀ v ∈c, v.2 =true) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      PathCover.Hamiltonian (actualGraph x).adj :=
  (finiteFormula_correct x hw hp).symm.trans (correct (finiteFormula x) _)

/-- A rejected syntax is mapped to a concrete non-Hamiltonian directed graph. -/
def invalidGraph : FiniteGraph := ⟨Fin 2,inferInstance,fun _ _ => False⟩

def validSyntax (x : CliffordComplexity.SatTy.denote) : Prop :=
  (∀ c∈x, c.length=3) ∧ (∀ c∈x, ∀ v∈c, v.2=true)
instance (x : CliffordComplexity.SatTy.denote) : Decidable (validSyntax x) := by
  unfold validSyntax
  infer_instance

def positiveGraph (x : CliffordComplexity.SatTy.denote) : FiniteGraph :=
  if validSyntax x then actualGraph x else invalidGraph

theorem positive_correct (x : CliffordComplexity.SatTy.denote) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      PathCover.Hamiltonian (positiveGraph x).adj := by
  by_cases hv : validSyntax x
  · rw [positiveGraph,ite_eq_left hv]
    exact actual_positive_correct x hv.1 hv.2
  · rw [positiveGraph,ite_eq_right hv]
    constructor
    · intro h
      obtain ⟨hp,hw,_⟩ := (CliffordComplexity.Concrete.monotoneOneInThree3Sat_iff x).mp h
      exact False.elim (hv ⟨hw,hp⟩)
    · rintro ⟨step,ho,ha⟩
      exact False.elim (ha (0 : Fin 2))

end GridHardness.CorrectedSatSchedule
