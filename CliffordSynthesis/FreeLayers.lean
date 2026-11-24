/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Circuit
public import Mathlib.Tactic

/-!
# Free Layers

Six one-qubit frames suffice for all free H/S words. Each parallel free
layer has a representative containing at most three gates per wire.
-/

@[expose] public section

namespace CliffordSynthesis.FreeLayers

open Circuit

variable {n : Nat}

def pair (a : Tableau n) (i : Fin n) (p : Fin n × Bool) : Bool × Bool := (a.x i p, a.z i p)

theorem tableau_ext {a b : Tableau n} (h : ∀ i p, pair a i p = pair b i p) : a = b := by
  have hx : a.x = b.x := funext fun i => funext fun p => congrArg Prod.fst (h i p)
  have hz : a.z = b.z := funext fun i => funext fun p => congrArg Prod.snd (h i p)
  cases a
  cases b
  cases hx
  cases hz
  rfl

/-- Identity, H, S, HS, SH, HSH, in execution order. -/
def act (f : Fin 6) (p : Bool × Bool) : Bool × Bool :=
  ![(p.1, p.2), (p.2, p.1), (p.1, p.2 ^^ p.1),
    (p.2, p.1 ^^ p.2), (p.2 ^^ p.1, p.1), (p.1 ^^ p.2, p.2)] f

def preH (f : Fin 6) : Fin 6 := ![1, 0, 3, 2, 5, 4] f
def preS (f : Fin 6) : Fin 6 := ![2, 4, 0, 5, 1, 3] f

theorem act_zero (p : Bool × Bool) : act 0 p = p := rfl
theorem act_preH : ∀ f p, act (preH f) p = act f (p.2, p.1) := by decide
theorem act_preS : ∀ f p, act (preS f) p = act f (p.1, p.2 ^^ p.1) := by decide

def applyFrames (f : Fin n → Fin 6) (a : Tableau n) : Tableau n where
  x i p := (act (f i) (pair a i p)).1
  z i p := (act (f i) (pair a i p)).2

theorem frames_zero (a : Tableau n) : applyFrames (fun _ => 0) a = a := rfl

theorem frames_preH (f : Fin n → Fin 6) (q : Fin n) (a : Tableau n) :
    applyFrames (Function.update f q (preH (f q))) a = applyFrames f (hadamard q a) := by
  apply tableau_ext
  intro i p
  by_cases hi : i = q
  · subst i
    simpa [pair, applyFrames, hadamard] using act_preH (f q) (pair a q p)
  · simp [pair, applyFrames, hadamard, hi]

theorem frames_preS (f : Fin n → Fin 6) (q : Fin n) (a : Tableau n) :
    applyFrames (Function.update f q (preS (f q))) a = applyFrames f (phase q a) := by
  apply tableau_ext
  intro i p
  by_cases hi : i = q
  · subst i
    simpa [pair, applyFrames, phase] using act_preS (f q) (pair a q p)
  · simp [pair, applyFrames, phase, hi]

def word (q : Fin n) (f : Fin 6) : List (Gate n) :=
  ![[], [.H q], [.S q], [.H q, .S q], [.S q, .H q], [.H q, .S q, .H q]] f

theorem word_length (q : Fin n) (f : Fin 6) : (word q f).length ≤ 3 := by
  fin_cases f <;> simp [word]

theorem word_cost (q : Fin n) (f : Fin 6) : cost (word q f) = 0 := by
  fin_cases f <;> rfl

theorem word_run (q : Fin n) (f : Fin 6) (a : Tableau n) (i : Fin n) (p : Fin n × Bool) :
    pair (run (word q f) a) i p = if i = q then act f (pair a i p) else pair a i p := by
  fin_cases f <;> by_cases hi : i = q <;>
    simp [word, run, applyGate, pair, hadamard, phase, act, hi, Bool.xor_comm]

def layerOn (f : Fin n → Fin 6) (qs : List (Fin n)) : List (Gate n) := qs.flatMap (fun q => word q (f q))

theorem layerOn_length (f : Fin n → Fin 6) (qs : List (Fin n)) :
    (layerOn f qs).length ≤ 3 * qs.length := by
  induction qs with
  | nil => simp [layerOn]
  | cons q qs ih =>
    have hw := word_length q (f q)
    change (word q (f q) ++ layerOn f qs).length ≤ _
    simp only [List.length_append, List.length_cons]
    omega

theorem layerOn_cost (f : Fin n → Fin 6) (qs : List (Fin n)) : cost (layerOn f qs) = 0 := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change cost (word q (f q) ++ layerOn f qs) = _
    rw [cost_append, word_cost, ih]

theorem layerOn_run (f : Fin n → Fin 6) (qs : List (Fin n)) (hn : qs.Nodup)
    (a : Tableau n) (i : Fin n) (p : Fin n × Bool) :
    pair (run (layerOn f qs) a) i p = if i ∈ qs then act (f i) (pair a i p) else pair a i p := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih =>
    change pair (run (word q (f q) ++ layerOn f qs) a) i p = _
    rw [run_append, ih (List.nodup_cons.mp hn).2, word_run]
    by_cases hi : i = q
    · subst i
      simp [List.nodup_cons.mp hn |>.1]
    · simp [hi]

def layer (f : Fin n → Fin 6) : List (Gate n) := layerOn f (List.finRange n)

theorem layer_length (f : Fin n → Fin 6) : (layer f).length ≤ 3 * n := by
  simpa [layer] using layerOn_length f (List.finRange n)

theorem layer_cost (f : Fin n → Fin 6) : cost (layer f) = 0 := layerOn_cost _ _

theorem layer_run (f : Fin n → Fin 6) (a : Tableau n) : run (layer f) a = applyFrames f a := by
  apply tableau_ext
  intro i p
  simpa [layer, applyFrames, pair] using layerOn_run f (List.finRange n) (List.nodup_finRange n) a i p

end CliffordSynthesis.FreeLayers
