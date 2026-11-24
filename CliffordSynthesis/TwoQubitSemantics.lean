/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.TwoQubitAlgebra
public import CliffordSynthesis.FreeSwaps

/-!
# Two Qubit Semantics

Embed a two-qubit map into any pair of distinct physical wires.
-/

@[expose] public section

namespace CliffordSynthesis.TwoQubit

open Circuit

variable {n : Nat}

def read (c t : Fin n) (a : Tableau n) (p : Fin n × Bool) : Bits :=
  (a.x c p, a.z c p, a.x t p, a.z t p)

def update (c t : Fin n) (f : Bits → Bits) (a : Tableau n) : Tableau n where
  x i p := if i = c then (f (read c t a p)).1 else
    if i = t then (f (read c t a p)).2.2.1 else a.x i p
  z i p := if i = c then (f (read c t a p)).2.1 else
    if i = t then (f (read c t a p)).2.2.2 else a.z i p

theorem read_update (c t : Fin n) (hct : c ≠ t) (f : Bits → Bits) (a : Tableau n) (p : Fin n × Bool) :
    read c t (update c t f a) p = f (read c t a p) := by
  simp [read, update, Ne.symm hct]

theorem update_comp (c t : Fin n) (hct : c ≠ t) (f g : Bits → Bits) (a : Tableau n) :
    update c t f (update c t g a) = update c t (f ∘ g) a := by
  apply FreeLayers.tableau_ext
  intro i p
  by_cases hic : i = c <;> by_cases hit : i = t <;>
    simp_all [FreeLayers.pair, update, read, Function.comp_apply, Ne.symm hct]

theorem update_id (c t : Fin n) (a : Tableau n) : update c t id a = a := by
  apply FreeLayers.tableau_ext
  intro i p
  by_cases hic : i = c <;> by_cases hit : i = t <;> simp_all [update, read, FreeLayers.pair]

def localWord (c t : Fin n) (f g : Fin 6) : List (Gate n) :=
  FreeLayers.word c f ++ FreeLayers.word t g

theorem localWord_cost (c t : Fin n) (f g : Fin 6) : cost (localWord c t f g) = 0 := by
  simp [localWord, cost_append, FreeLayers.word_cost]

theorem localWord_run (c t : Fin n) (hct : c ≠ t) (f g : Fin 6) (a : Tableau n) :
    run (localWord c t f g) a = update c t (localAction f g) a := by
  apply FreeLayers.tableau_ext
  intro i p
  rw [localWord, run_append, FreeLayers.word_run, FreeLayers.word_run]
  by_cases hic : i = c
  · subst i
    simp [FreeLayers.pair, update, read, localAction, hct]
  · by_cases hit : i = t
    · subst i
      simp [FreeLayers.pair, update, read, localAction, Ne.symm hct]
    · simp [FreeLayers.pair, update, hic, hit]

theorem cnot_update (c t : Fin n) (hct : c ≠ t) (a : Tableau n) :
    cnot c t a = update c t cnotAction a := by
  apply FreeLayers.tableau_ext
  intro i p
  by_cases hic : i = c <;> by_cases hit : i = t <;>
    simp_all [FreeLayers.pair, cnot, update, cnotAction, read]

theorem swap_update (c t : Fin n) (hct : c ≠ t) (a : Tableau n) :
    FreeSwaps.reorder (Equiv.swap c t) a = update c t swapAction a := by
  apply FreeLayers.tableau_ext
  intro i p
  by_cases hic : i = c
  · subst i
    simp [FreeLayers.pair, FreeSwaps.reorder, update, swapAction, read]
  · by_cases hit : i = t
    · subst i
      simp [FreeLayers.pair, FreeSwaps.reorder, update, swapAction, read, Ne.symm hct]
    · simp [FreeLayers.pair, FreeSwaps.reorder, update, hic, hit, Equiv.swap_apply_of_ne_of_ne hic hit]

/-- A literal circuit for the finite normal form. -/
def normalSteps (c t : Fin n) (hct : c ≠ t) (f : Normal) : List (FreeSwaps.Step n) :=
  (localWord c t f.before₀ f.before₁).map .gate ++
  (if f.cnot then [.gate (.CX c t hct)] else []) ++
  (localWord c t f.after₀ f.after₁).map .gate ++
  (if f.swap then [.swap c t] else [])

theorem normalSteps_cost (c t : Fin n) (hct : c ≠ t) (f : Normal) :
    FreeSwaps.count (normalSteps c t hct f) ≤ 1 := by
  simp only [normalSteps, FreeSwaps.count_append, FreeSwaps.count_embed, localWord_cost, Nat.zero_add,
    Nat.add_zero]
  cases f.cnot <;> cases f.swap <;> simp [FreeSwaps.count, paid]

theorem normalSteps_run (c t : Fin n) (hct : c ≠ t) (f : Normal) (a : Tableau n) :
    FreeSwaps.execute (normalSteps c t hct f) a = update c t (normalAction f) a := by
  simp only [normalSteps, FreeSwaps.execute_append, FreeSwaps.execute_embed, localWord_run c t hct]
  cases hc : f.cnot <;> cases hs : f.swap <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, FreeSwaps.execute, applyGate,
      cnot_update c t hct, swap_update c t hct, update_comp c t hct]
  all_goals congr 1; funext v; simp [normalAction, hc, hs]

end CliffordSynthesis.TwoQubit
