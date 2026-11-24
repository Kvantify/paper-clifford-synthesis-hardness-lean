/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleRun
public import GridHardness.SatXorInterface
public import GridHardness.PlanarSatReduction

/-!
# Corrected SAT Graph

Actual finite SAT graphs obtained by iterating the XOR-line
construction. Every later move acts on the explicitly retained original XORs
or on newly created sections; the required edge isolation is proved, not
assumed of the eventual Hamiltonian cycle. A geometric schedule is separate.
-/

@[expose] public section

namespace GridHardness.CorrectedSatGraph
open PlanarSatAssembly XorLineSchedule

/-- The original occurrence family, with exact incident-edge isolation. -/
def family {n m : Nat} (φ : Formula n m) : Family (Adj φ) (Occurrence m) where
  embed := xor
  injective := by
    rintro ⟨o,i⟩ ⟨p,j⟩ h
    simpa [PlanarSatAssembly.xor] using h
  isolated := by
    intro o
    constructor
    · exact xor_internal_iff φ o
    · intro i hi0 hi7 v hv
      obtain ⟨e,_,he⟩ := xor_outgoing φ o i hi0 hi7 v hv
      exact ⟨(XorGadget.arc e).2,he⟩
    · intro j hj3 hj4 v hv
      obtain ⟨e,_,he⟩ := xor_incoming φ o j hj3 hj4 v hv
      exact ⟨(XorGadget.arc e).1,he⟩

/-- The construction depends on the formula and the named finite plan only. -/
def graph {n m : Nat} (φ : Formula n m) (p : Plan (Occurrence m)) : FiniteGraph :=
  run p (Adj φ) (family φ)

/-- SAT equivalence for the actual recursively constructed graph. No source
isolation or traversal conditions remain in this endpoint. -/
theorem correct {n m : Nat} (φ : Formula n m) (p : Plan (Occurrence m)) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ p).adj :=
  (PlanarSatReduction.correct φ).trans (run_correct p (Adj φ) (family φ))

theorem vertex_count {n m : Nat} (φ : Formula n m) (p : Plan (Occurrence m)) :
    Nat.card (graph φ p).Vertex=3+2*n+36*m+40*p.length := by
  rw [graph,run_vertex_count,Nat.card_eq_fintype_card,PlanarSatAssembly.vertex_card]

/-- Three-literal clauses may repeat a variable. -/
theorem positiveSat_correct (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈ x, c.length =3) (hp : ∀ c ∈ x, ∀ v ∈ c, v.2 =true)
    (p : Plan (Occurrence x.length)) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      PathCover.Hamiltonian (graph (finiteFormula x) p).adj :=
  (finiteFormula_correct x hw hp).symm.trans (correct (finiteFormula x) p)

/-- A concrete two-move example: refine one line across a second occurrence,
then refine its first new section across a third untouched occurrence. -/
def twoMoves {m : Nat} (a b c : Occurrence m)
    (hab : a ≠b) (hca : c ≠a) (hcb : c ≠b) : Plan (Occurrence m) :=
  .cross a b hab (.cross (.inr 0) (.inl ⟨c,hca,hcb⟩) (by intro h; cases h) .done)

theorem twoMoves_correct {n m : Nat} (φ : Formula n m) (a b c : Occurrence m)
    (hab : a ≠b) (hca : c ≠a) (hcb : c ≠b) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ (twoMoves a b c hab hca hcb)).adj :=
  correct φ _

theorem twoMoves_vertex_count {n m : Nat} (φ : Formula n m) (a b c : Occurrence m)
    (hab : a ≠b) (hca : c ≠a) (hcb : c ≠b) :
    Nat.card (graph φ (twoMoves a b c hab hca hcb)).Vertex=3+2*n+36*m+80 := by
  rw [vertex_count]
  rfl

end GridHardness.CorrectedSatGraph
