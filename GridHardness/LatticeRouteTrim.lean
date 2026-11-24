/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteDirections

/-!
# Lattice Route Trim

Removing a bounded initial and terminal portion of a lattice path.
The surviving endpoints are identified by their original list indices.
-/

@[expose] public section

namespace GridHardness.LatticeRouteTrim
set_option autoImplicit false

variable {α : Type*}

def trim (a b : Nat) (l : List α) : List α :=
  (l.drop a).take (l.length-a-b)

theorem length (a b : Nat) (l : List α) :
    (trim a b l).length=l.length-a-b := by
  simp [trim]

theorem sublist (a b : Nat) (l : List α) : List.Sublist (trim a b l) l :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

theorem nodup (a b : Nat) (l : List α) (hn : l.Nodup) : (trim a b l).Nodup :=
  hn.sublist (sublist a b l)

theorem chain {R : α → α → Prop} (a b : Nat) (l : List α) (hc : l.IsChain R) :
    (trim a b l).IsChain R := (hc.drop a).take _

theorem getElem (a b : Nat) (l : List α) (i : Nat) (hi : i <(trim a b l).length) :
    (trim a b l)[i]=l[a+i]'(by rw [length] at hi; omega) := by
  simp [trim]

theorem head (a b : Nat) (l : List α) (h : a +b<l.length) :
    (trim a b l).head?=some (l[a]'(by omega)) := by
  rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by rw [length]; omega),getElem]
  simp

theorem getLast (a b : Nat) (l : List α) (h : a +b<l.length) :
    (trim a b l).getLast?=some (l[l.length-1-b]'(by omega)) := by
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by rw [length]; omega),getElem]
  congr 2
  rw [length]
  omega

theorem mem (a b : Nat) (l : List α) (q : α) (h : q ∈trim a b l) : q∈l :=
  (sublist a b l).subset h

end GridHardness.LatticeRouteTrim
