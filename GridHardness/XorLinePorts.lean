/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineSource

/-!
# XOR Line Ports

Locate the selected input and output ports in a two-channel XOR line.
-/

@[expose] public section

namespace GridHardness.XorLine

/-- Two alternative original endpoints, and one compulsory crossed-arc port
per row. The row ports have no duplicated or independently chosen Boolean. -/
abbrev Port (n : Nat) := Bool ⊕ Fin n
def selected {n : Nat} (choice : Bool) : Channel n → Port n
  | none => .inl choice
  | some i => .inr i

def inputPort (n : Nat) : Port n → Vertex n
  | .inl b => x (if b then 0 else Fin.last n) (if b then 3 else 4)
  | .inr i => row i false
def outputPort (n : Nat) : Port n → Vertex n
  | .inl b => x (if b then 0 else Fin.last n) (if b then 0 else 7)
  | .inr i => row i true

theorem inputPort_injective (n : Nat) : Function.Injective (inputPort n) := by
  rintro (b | i) (c | j) h
  · cases b <;> cases c <;> simp [inputPort,x] at h ⊢
  · cases b <;> simp [inputPort,x,row] at h
  · cases c <;> simp [inputPort,x,row] at h
  · simpa [inputPort,row] using h

theorem outputPort_injective (n : Nat) : Function.Injective (outputPort n) := by
  rintro (b | i) (c | j) h
  · cases b <;> cases c <;> simp [outputPort,x] at h ⊢
  · cases b <;> simp [outputPort,x,row] at h
  · cases c <;> simp [outputPort,x,row] at h
  · simpa [outputPort,row] using h

theorem inputPort_isInput (n : Nat) (p : Port n) : IsInput n (inputPort n p) := by
  cases p with
  | inl b => cases b <;> simp [IsInput,inputPort,x]
  | inr i => rfl

theorem outputPort_isOutput (n : Nat) (p : Port n) : IsOutput n (outputPort n p) := by
  cases p with
  | inl b => cases b <;> simp [IsOutput,outputPort,x]
  | inr i => rfl

theorem cover_first_port (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).first i=inputPort n (selected choice i) := by
  cases i with
  | none => rw [cover_first]; cases choice <;> rfl
  | some i => rfl

theorem cover_finish_port (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).finish i=outputPort n (selected choice i) := by
  cases i with
  | none => rw [cover_finish]; cases choice <;> rfl
  | some i => rfl

theorem no_output_input_edge (n : Nat) (p q : Port n) :
    ¬Adj n (outputPort n p) (inputPort n q) := by
  have hh : ∀ b c : Bool,
      ¬∃ e : Fin 10, XorGadget.arc e=((if b then 0 else 7),(if c then 3 else 4)) := by decide
  cases p with
  | inl b =>
    cases q with
    | inl c => exact fun h => hh b c h.2
    | inr j => cases b <;> simp [Adj,outputPort,inputPort,row,x]
  | inr i =>
    cases q with
    | inl c => cases c <;> simp [Adj,outputPort,inputPort,row,x]
    | inr j => simp [Adj,outputPort,inputPort,row,x]

namespace Source

def inputPort (n : Nat) : Port n → Vertex n
  | .inl b => .inl (if b then 3 else 4)
  | .inr i => .inr (i,false)
def outputPort (n : Nat) : Port n → Vertex n
  | .inl b => .inl (if b then 0 else 7)
  | .inr i => .inr (i,true)

theorem inputPort_injective (n : Nat) : Function.Injective (inputPort n) := by
  rintro (b | i) (c | j) h
  · cases b <;> cases c <;> simp [inputPort] at h ⊢
  · cases b <;> simp [inputPort] at h
  · cases c <;> simp [inputPort] at h
  · simpa [inputPort] using h

theorem outputPort_injective (n : Nat) : Function.Injective (outputPort n) := by
  rintro (b | i) (c | j) h
  · cases b <;> cases c <;> simp [outputPort] at h ⊢
  · cases b <;> simp [outputPort] at h
  · cases c <;> simp [outputPort] at h
  · simpa [outputPort] using h

theorem inputPort_isInput (n : Nat) (p : Port n) : IsInput n (inputPort n p) := by
  cases p with
  | inl b => cases b <;> simp [IsInput,inputPort]
  | inr i => rfl

theorem outputPort_isOutput (n : Nat) (p : Port n) : IsOutput n (outputPort n p) := by
  cases p with
  | inl b => cases b <;> simp [IsOutput,outputPort]
  | inr i => rfl

theorem cover_first_port (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).first i=inputPort n (selected choice i) := by
  cases i with
  | none => cases choice <;> rfl
  | some i => rfl

theorem cover_finish_port (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).finish i=outputPort n (selected choice i) := by
  cases i with
  | none => cases choice <;> rfl
  | some i => rfl

theorem no_output_input_edge (n : Nat) (p q : Port n) :
    ¬Adj n (outputPort n p) (inputPort n q) := by
  have hh : ∀ b c : Bool,
      ¬∃ e : Fin 10, XorGadget.arc e=((if b then 0 else 7),(if c then 3 else 4)) := by decide
  cases p with
  | inl b =>
    cases q with
    | inl c => exact hh b c
    | inr j => cases b <;> simp [Adj,outputPort,inputPort]
  | inr i =>
    cases q with
    | inl c => cases c <;> simp [Adj,outputPort,inputPort]
    | inr j => simp [Adj,outputPort,inputPort]

end Source
end GridHardness.XorLine
