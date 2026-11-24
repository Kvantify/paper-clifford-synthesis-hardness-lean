/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLine
public import GridHardness.XorWirePaths

/-!
# XOR Line Paths

Number the channels, sections, and row positions of an XOR line.
-/

@[expose] public section

namespace GridHardness.XorLine
open PathCover

abbrev Channel (n : Nat) := Option (Fin n)
def size {n : Nat} : Channel n → Nat | none => 7 | some _ => 9

/-- The original path takes the first section in the true case and the last
section in the false case. Every other section belongs to one crossed arc. -/
def sectionEquiv (n : Nat) (choice : Bool) : Channel n ≃ Fin (n+1) :=
  (finSuccEquiv' (if choice then 0 else Fin.last n)).symm

@[simp] theorem section_none (n : Nat) (choice : Bool) :
    sectionEquiv n choice none = if choice then 0 else Fin.last n :=
  finSuccEquiv'_symm_none _

@[simp] theorem section_some {n : Nat} (choice : Bool) (i : Fin n) :
    sectionEquiv n choice (some i) = if choice then i.succ else i.castSucc := by
  cases choice
  · exact finSuccEquiv'_symm_some_below (by exact i.castSucc_lt_last)
  · exact finSuccEquiv'_symm_some_above (Fin.zero_le _)

def blockEquiv (n : Nat) : Blocks (@size n) ≃ (Fin 8 ⊕ (Fin n × Fin 10)) where
  toFun := fun w => match w with | ⟨none,j⟩ => .inl j | ⟨some i,j⟩ => .inr (i,j)
  invFun := fun w => match w with | .inl j => ⟨none,j⟩ | .inr (i,j) => ⟨some i,j⟩
  left_inv := by rintro ⟨_ | i,j⟩ <;> rfl
  right_inv := by rintro (j | ⟨i,j⟩) <;> rfl

def rowSlot : Fin 10 ≃ (Bool ⊕ Fin 8) where
  toFun := ![.inl false,.inr 0,.inr 1,.inr 2,.inr 3,.inr 4,.inr 5,.inr 6,.inr 7,.inl true]
  invFun := fun w => match w with | .inl false => 0 | .inl true => 9 | .inr j => ⟨j.val+1,by omega⟩
  left_inv := by decide
  right_inv := by decide

def slotEquiv (n : Nat) : (Fin 8 ⊕ (Fin n × Fin 10)) ≃
    ((Channel n × Fin 8) ⊕ (Fin n × Bool)) where
  toFun := fun w => match w with
    | .inl j => .inl (none,j)
    | .inr (i,j) => match rowSlot j with | .inl b => .inr (i,b) | .inr k => .inl (some i,k)
  invFun := fun w => match w with
    | .inl (none,j) => .inl j
    | .inl (some i,j) => .inr (i,rowSlot.symm (.inr j))
    | .inr (i,b) => .inr (i,rowSlot.symm (.inl b))
  left_inv := by
    rintro (j | ⟨i,j⟩)
    · rfl
    · fin_cases j <;> rfl
  right_inv := by
    rintro (⟨_ | i,j⟩ | ⟨i,b⟩)
    · rfl
    · fin_cases j <;> rfl
    · cases b <;> rfl

def cover (n : Nat) (choice : Bool) : Cover (Channel n) (Vertex n) where
  size := size
  equiv := (blockEquiv n).trans ((slotEquiv n).trans
    (Equiv.sumCongr (Equiv.prodCongr (sectionEquiv n choice) (XorWire.localOrder choice))
      (Equiv.refl _)))

theorem cover_none (n : Nat) (choice : Bool) (j : Fin 8) :
    (cover n choice).equiv ⟨none,j⟩ = x (sectionEquiv n choice none) (XorWire.localOrder choice j) := rfl

theorem cover_row_first {n : Nat} (choice : Bool) (i : Fin n) :
    (cover n choice).equiv ⟨some i,0⟩ = row i false := rfl
theorem cover_row_last {n : Nat} (choice : Bool) (i : Fin n) :
    (cover n choice).equiv ⟨some i,9⟩ = row i true := rfl
theorem cover_row_inside {n : Nat} (choice : Bool) (i : Fin n) (j : Fin 8) :
    (cover n choice).equiv ⟨some i,⟨j.val+1,by change j.val+1<10; omega⟩⟩ =
      x (sectionEquiv n choice (some i)) (XorWire.localOrder choice j) := by
  fin_cases j <;> rfl

def input (n : Nat) (choice : Bool) : Channel n → Vertex n
  | none => x (sectionEquiv n choice none) (XorWire.localOrder choice 0)
  | some i => row i false
def output (n : Nat) (choice : Bool) : Channel n → Vertex n
  | none => x (sectionEquiv n choice none) (XorWire.localOrder choice 7)
  | some i => row i true

theorem cover_first (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).first i = input n choice i := by cases i <;> rfl
theorem cover_finish (n : Nat) (choice : Bool) (i : Channel n) :
    (cover n choice).finish i = output n choice i := by cases i <;> rfl

/-- Each cover has one original XOR route and one route for every crossed
arc. Its equivalence proves disjointness and exhaustive vertex coverage. -/
theorem cover_internalEdges (n : Nat) (choice : Bool) (R : Vertex n → Vertex n → Prop)
    (hlocal : ∀ (i : Fin (n +1)) (j : Fin 7),
      R (x i (XorWire.localOrder choice j.castSucc)) (x i (XorWire.localOrder choice j.succ)))
    (hin : ∀ i : Fin n, R (row i false)
      (x (sectionEquiv n choice (some i)) (XorWire.localOrder choice 0)))
    (hout : ∀ i : Fin n,
      R (x (sectionEquiv n choice (some i)) (XorWire.localOrder choice 7)) (row i true)) :
    (cover n choice).InternalEdges R := by
  rintro (_ | i) j
  · exact hlocal _ j
  · change Fin 9 at j
    fin_cases j
    · exact hin i
    · exact hlocal _ 0
    · exact hlocal _ 1
    · exact hlocal _ 2
    · exact hlocal _ 3
    · exact hlocal _ 4
    · exact hlocal _ 5
    · exact hlocal _ 6
    · exact hout i

theorem cover_adjacent (n : Nat) (choice : Bool) : (cover n choice).InternalEdges (Adj n) := by
  apply cover_internalEdges
  · intro i j
    obtain ⟨e,_,he⟩ := XorWire.local_route_steps choice j
    exact ⟨rfl,e,he⟩
  · intro i
    rw [section_some]
    cases choice
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · intro i
    rw [section_some]
    cases choice
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩

end GridHardness.XorLine
