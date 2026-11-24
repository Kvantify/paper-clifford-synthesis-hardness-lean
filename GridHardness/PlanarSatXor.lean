/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatAssembly

/-!
# Planar SAT XOR

Extracting the actual XOR choices of a Hamiltonian successor in the
assembled graph. Degree and closed-component hypotheses of the finite XOR
certificate are discharged here from the graph constructor and its global
Hamiltonian permutation, rather than left as assembly promises.
-/

@[expose] public section

namespace GridHardness.PlanarSatXor

open XorGadget

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
/-- A finite reformulation of the one-in/one-out constraints convenient
for applying injectivity of a global successor. -/
theorem degree_iff : ∀ b : Selection, DegreeOK b ↔
    (∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
      ∃ e : Fin 10, (arc e).1 = i ∧ b e = true) ∧
    (∀ i : Fin 8, i ≠ 3 → i ≠ 4 →
      ∃ e : Fin 10, (arc e).2 = i ∧ b e = true) ∧
    (∀ e f : Fin 10, b e = true → b f = true →
      (arc e).1 = (arc f).1 → (arc e).2 = (arc f).2) ∧
    (∀ e f : Fin 10, b e = true → b f = true →
      (arc e).2 = (arc f).2 → (arc e).1 = (arc f).1) := by
  decide

def selection {V : Type*} [DecidableEq V] (succ : V → V) (embed : Fin 8 → V) : Selection :=
  fun e => decide (succ (embed (arc e).1) = embed (arc e).2)

@[simp] theorem selection_true {V : Type*} [DecidableEq V]
    (succ : V → V) (embed : Fin 8 → V) (e : Fin 10) :
    selection succ embed e = true ↔ succ (embed (arc e).1) = embed (arc e).2 := by
  simp [selection]

/-- Isolation at the four ports suffices to recover all degree constraints. -/
theorem degree_of_isolation {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (embed : Fin 8 → V) (hinj : Function.Injective embed)
    (hout : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 →
      ∃ e : Fin 10, (arc e).1 = i ∧ succ (embed i) = embed (arc e).2)
    (hin : ∀ i : Fin 8, i ≠ 3 → i ≠ 4 →
      ∃ e : Fin 10, (arc e).2 = i ∧ succ (embed (arc e).1) = embed i) :
    DegreeOK (selection succ embed) := by
  rw [degree_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi0 hi7
    obtain ⟨e, he, hs⟩ := hout i hi0 hi7
    exact ⟨e, he, (selection_true _ _ _).mpr (by simpa [he] using hs)⟩
  · intro i hi3 hi4
    obtain ⟨e, he, hs⟩ := hin i hi3 hi4
    exact ⟨e, he, (selection_true _ _ _).mpr (by simpa [he] using hs)⟩
  · intro e f he hf hsrc
    apply hinj
    rw [← (selection_true _ _ _).mp he, ← (selection_true _ _ _).mp hf, hsrc]
  · intro e f he hf hdst
    apply hinj
    apply succ.injective
    rw [(selection_true _ _ _).mp he, (selection_true _ _ _).mp hf, hdst]

open PlanarSatAssembly

/-- Every XOR occurring in the concrete SAT graph traverses exactly its
left or right Hamiltonian route in any global Hamiltonian cycle. -/
theorem assembly_selection {n m : Nat} (φ : Formula n m)
    (succ : Equiv.Perm (Vertex n m)) (horbit : OneOrbit succ)
    (hadj : ∀ v, Adj φ v (succ v)) (o : Occurrence m) :
    selection succ (xor o) = leftRoute ∨ selection succ (xor o) = rightRoute := by
  have hdegree : DegreeOK (selection succ (xor o)) := by
    apply degree_of_isolation succ (xor o) (xor_injective o)
    · intro i hi0 hi7
      exact xor_outgoing φ o i hi0 hi7 _ (hadj (xor o i))
    · intro i hi3 hi4
      obtain ⟨e, he, hs⟩ := xor_incoming φ o i hi3 hi4 (succ.symm (xor o i))
        (by simpa using hadj (succ.symm (xor o i)))
      exact ⟨e, he, by rw [← hs, succ.apply_symm_apply]⟩
  exact XorGadget.selection_of_oneOrbit succ horbit (xor o) (sent 0)
    (fun v => by simp [sent, PlanarSatAssembly.xor]) (selection succ (xor o)) hdegree
    (fun e he => (selection_true _ _ _).mp he)

end GridHardness.PlanarSatXor
