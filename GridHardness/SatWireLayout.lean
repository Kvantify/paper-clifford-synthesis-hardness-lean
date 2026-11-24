/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatXorInterface
public import GridHardness.PermutationWireLayout
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# SAT Wire Layout

A bounded crossing schedule for SAT occurrence wires. Variable-side
order groups occurrences by variable; clause-side order uses clause and
position indices. This module locates crossings of wire centerlines.
Crossover bodies and the other graph vertices have separate placement modules.
-/

@[expose] public section

namespace GridHardness.SatWireLayout
open PlanarSatAssembly

/-- The exact order in which occurrences appear along the variable chains. -/
def variableOrder {n m : Nat} (φ : Formula n m) : List (Occurrence m) :=
  (List.finRange n).flatMap (occurrencesOf φ)

theorem variableOrder_nodup {n m : Nat} (φ : Formula n m) : (variableOrder φ).Nodup := by
  rw [variableOrder, List.nodup_flatMap]
  constructor
  · intro v _
    exact occurrencesOf_nodup φ v
  · apply (List.nodup_finRange n).imp
    intro v w hvw
    apply List.disjoint_left.mpr
    intro o hv hw
    exact hvw (((mem_occurrencesOf φ v o).mp hv).symm.trans
      ((mem_occurrencesOf φ w o).mp hw))

theorem mem_variableOrder {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    o ∈ variableOrder φ := by
  apply List.mem_flatMap.mpr
  exact ⟨φ o.1 o.2, List.mem_finRange _, (mem_occurrencesOf _ _ _).mpr rfl⟩

def variableOrderEquiv {n m : Nat} (φ : Formula n m) :
    Fin (variableOrder φ).length ≃ Occurrence m :=
  List.Nodup.getEquivOfForallMemList _ (variableOrder_nodup φ) (mem_variableOrder φ)

theorem variableOrder_length {n m : Nat} (φ : Formula n m) :
    (variableOrder φ).length = 3*m := by
  have h := Fintype.card_congr (variableOrderEquiv φ)
  simpa [Occurrence, Nat.mul_comm] using h

/-- Position in the variable-grouped boundary order. This is computed by
list search over exactly `3*m` occurrences, not over variable-label magnitudes. -/
def variableRank {n m : Nat} (φ : Formula n m) : Occurrence m ≃ Fin (3*m) :=
  (variableOrderEquiv φ).symm.trans (finCongr (variableOrder_length φ))

/-- Position in clause order, with the three literal slots consecutive. -/
def clauseRank (m : Nat) : Occurrence m ≃ Fin (3*m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 3))

@[simp] theorem variableRank_val {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    (variableRank φ o).val = @List.idxOf (Occurrence m) instBEqOfDecidableEq o (variableOrder φ) := by
  simp [variableRank, variableOrderEquiv]

@[simp] theorem clauseRank_val {m : Nat} (o : Occurrence m) :
    (clauseRank m o).val = o.1.val*3 + o.2.val := by
  simp [clauseRank, Nat.mul_comm, Nat.add_comm]

def permutation {n m : Nat} (φ : Formula n m) : Equiv.Perm (Fin (3*m)) :=
  (variableRank φ).symm.trans (clauseRank m)

@[simp] theorem permutation_rank {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    permutation φ (variableRank φ o) = clauseRank m o := by simp [permutation]

def OnWire {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (q : PermutationWireLayout.Point) : Prop :=
  PermutationWireLayout.OnWire (permutation φ) (variableRank φ o) q

def crossing {n m : Nat} (φ : Formula n m) (o p : Occurrence m) :
    PermutationWireLayout.Point :=
  PermutationWireLayout.crossing (permutation φ) (variableRank φ o) (variableRank φ p)

/-- Every crossing is determined just by reversing two occurrence orders. -/
theorem intersection_iff {n m : Nat} (φ : Formula n m) (o p : Occurrence m)
    (hop : variableRank φ o < variableRank φ p) (q : PermutationWireLayout.Point) :
    (OnWire φ o q ∧ OnWire φ p q) ↔
      (clauseRank m p < clauseRank m o ∧ q = crossing φ o p) := by
  simpa [OnWire, crossing, PermutationWireLayout.crossing] using
    PermutationWireLayout.intersection_iff (permutation φ) hop q

theorem no_third_wire {n m : Nat} (φ : Formula n m) (o p q : Occurrence m)
    (hop : variableRank φ o < variableRank φ p) (hpo : clauseRank m p < clauseRank m o)
    (hq : OnWire φ q (crossing φ o p)) : q = o ∨ q = p := by
  have h := PermutationWireLayout.no_third_wire (permutation φ) hop
    (by simpa using hpo) (variableRank φ q) hq
  exact h.imp (fun he => (variableRank φ).injective he) (fun he => (variableRank φ).injective he)

theorem in_box {n m : Nat} (φ : Formula n m) (o : Occurrence m)
    (q : PermutationWireLayout.Point) (hq : OnWire φ o q) :
    0 ≤ q.1 ∧ q.1 ≤ 3*(m : Int)+1 ∧ 1 ≤ q.2 ∧ q.2 ≤ 6*(m : Int)+1 := by
  have h := PermutationWireLayout.in_box (permutation φ) (variableRank φ o) q hq
  push_cast at h
  omega

theorem crossing_count {n m : Nat} (φ : Formula n m) :
    (PermutationWireLayout.crossings (permutation φ)).card ≤ 9*m*m := by
  have h := PermutationWireLayout.crossing_count (permutation φ)
  nlinarith

end GridHardness.SatWireLayout
