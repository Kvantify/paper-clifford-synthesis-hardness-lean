/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCodeEval

/-!
# XOR Wire Code Adequacy

Number the outer, cell, and section vertices of the XOR wire replacement.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorWireCode
open CliffordComplexity

abbrev Outer (x : InputTy.denote) := Fin x.1.1.length
abbrev Cell (x : InputTy.denote) := Fin x.2.1.length
abbrev Section (L : Code InputTy NatListTy) (x : InputTy.denote) := Fin ((L.eval x).length + 1)
abbrev V (L : Code InputTy NatListTy) (x : InputTy.denote) :=
  Outer x ⊕ (Cell x × XorWire.Vertex (L.eval x).length)

def numbering (L : Code InputTy NatListTy) (x : InputTy.denote) : Numbering (V L x) :=
  (Numbering.fin x.1.1.length).sum
    ((Numbering.fin x.2.1.length).prod ((Numbering.fin ((L.eval x).length + 1)).prod (Numbering.fin 8)))

def outer (L : Code InputTy NatListTy) (x : InputTy.denote) (u : Outer x) : V L x := Sum.inl u
def wire (L : Code InputTy NatListTy) (x : InputTy.denote)
    (c : Cell x) (s : Section L x) (j : Fin 8) : V L x := Sum.inr (c,(s,j))
def inputVertex (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Cell x) (b : Bool) : V L x :=
  Sum.inr (c,XorWire.entry (L.eval x).length b)
def outputVertex (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Cell x) (b : Bool) : V L x :=
  Sum.inr (c,XorWire.exit (L.eval x).length b)

@[simp] theorem num_outer (L : Code InputTy NatListTy) (x : InputTy.denote) (u : Outer x) :
    (numbering L x).num (outer L x u) = u.val := rfl
@[simp] theorem num_wire (L : Code InputTy NatListTy) (x : InputTy.denote)
    (c : Cell x) (s : Section L x) (j : Fin 8) :
    (numbering L x).num (wire L x c s j) =
      wireNum x.1.1.length (L.eval x).length c.val s.val j.val := rfl
@[simp] theorem num_input (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Cell x) (b : Bool) :
    (numbering L x).num (inputVertex L x c b) = inNum L x c.val b := by cases b <;> rfl
@[simp] theorem num_output (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Cell x) (b : Bool) :
    (numbering L x).num (outputVertex L x c b) = outNum L x c.val b := by cases b <;> rfl

def outside (x : InputTy.denote) (a b : Outer x) : Prop := (a.val,b.val) ∈ x.1.2.1
def enter (x : InputTy.denote) (a : Outer x) (c : Cell x) (b : Bool) : Prop :=
  (a.val,(c.val,b)) ∈ x.2.2.2.1
def leave (x : InputTy.denote) (c : Cell x) (b : Bool) (a : Outer x) : Prop :=
  (a.val,(c.val,b)) ∈ x.2.2.2.2.1
def link (x : InputTy.denote) (c : Cell x) (b : Bool) (d : Cell x) (s : Bool) : Prop :=
  ((c.val,b),(d.val,s)) ∈ x.2.2.2.2.2

def OutsideArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ u v : Outer x, outside x u v ∧ a = outer L x u ∧ b = outer L x v
def InternalArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ (c : Cell x) (s : Section L x) (e : Fin 10),
    a = wire L x c s (XorGadget.arc e).1 ∧ b = wire L x c s (XorGadget.arc e).2
def WireLinkArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ (c : Cell x) (i : Fin (L.eval x).length),
    (a = wire L x c i.castSucc 0 ∧ b = wire L x c i.succ 3) ∨
    (a = wire L x c i.succ 7 ∧ b = wire L x c i.castSucc 4)
def EnterArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ (u : Outer x) (c : Cell x) (s : Bool),
    enter x u c s ∧ a = outer L x u ∧ b = inputVertex L x c s
def LeaveArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ (u : Outer x) (c : Cell x) (s : Bool),
    leave x c s u ∧ a = outputVertex L x c s ∧ b = outer L x u
def LinkArc (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) : Prop :=
  ∃ (c d : Cell x) (s t : Bool), c ≠ d ∧ link x c s d t ∧
    a = outputVertex L x c s ∧ b = inputVertex L x d t

theorem encoded_pair_eq (L : Code InputTy NatListTy) (x : InputTy.denote) (a b u v : V L x) :
    ((numbering L x).num u,(numbering L x).num v) =
      ((numbering L x).num a,(numbering L x).num b) ↔ a = u ∧ b = v := by
  constructor
  · intro h
    constructor
    · apply (numbering L x).num_inj
      exact (congrArg Prod.fst h).symm
    · apply (numbering L x).num_inj
      exact (congrArg Prod.snd h).symm
  · rintro ⟨rfl,rfl⟩; rfl

theorem numbered_outside (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ outsideCode.eval x ↔ OutsideArc L x a b := by
  rw [mem_outsideCode]
  constructor
  · rintro ⟨hm,ha,hb⟩
    let u : Outer x := ⟨(numbering L x).num a,ha⟩
    let v : Outer x := ⟨(numbering L x).num b,hb⟩
    exact ⟨u,v,hm,(numbering L x).num_inj rfl,(numbering L x).num_inj rfl⟩
  · rintro ⟨u,v,hm,rfl,rfl⟩
    exact ⟨hm,u.isLt,v.isLt⟩

theorem numbered_internal (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ (internalCode L).eval x ↔
      InternalArc L x a b := by
  rw [mem_internalCode]
  constructor
  · rintro ⟨⟨c,s⟩,⟨hc,hs⟩,e,he⟩
    exact ⟨⟨c,hc⟩,⟨s,hs⟩,e,(encoded_pair_eq L x a b _ _).mp he⟩
  · rintro ⟨c,s,e,rfl,rfl⟩
    exact ⟨(c.val,s.val),⟨c.isLt,s.isLt⟩,e,rfl⟩

theorem numbered_wireLinks (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ (wireLinksCode L).eval x ↔
      WireLinkArc L x a b := by
  rw [mem_wireLinksCode]
  constructor
  · rintro ⟨⟨c,i⟩,⟨hc,hi⟩,h | h⟩
    · exact ⟨⟨c,hc⟩,⟨i,hi⟩,Or.inl ((encoded_pair_eq L x a b _ _).mp h.symm)⟩
    · exact ⟨⟨c,hc⟩,⟨i,hi⟩,Or.inr ((encoded_pair_eq L x a b _ _).mp h.symm)⟩
  · rintro ⟨c,i,h | h⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨(c.val,i.val),⟨c.isLt,i.isLt⟩,Or.inl rfl⟩
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨(c.val,i.val),⟨c.isLt,i.isLt⟩,Or.inr rfl⟩

theorem numbered_enter (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ (enterCode L).eval x ↔ EnterArc L x a b := by
  rw [mem_enterCode]
  constructor
  · rintro ⟨⟨u,c,s⟩,hm,⟨hu,hc⟩,he⟩
    refine ⟨⟨u,hu⟩,⟨c,hc⟩,s,hm,?_⟩
    apply (encoded_pair_eq L x a b _ _).mp
    rw [num_outer, num_input]
    exact he
  · rintro ⟨u,c,s,hm,rfl,rfl⟩
    refine ⟨(u.val,(c.val,s)),hm,⟨u.isLt,c.isLt⟩,?_⟩
    rw [num_outer, num_input]

theorem numbered_leave (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ (leaveCode L).eval x ↔ LeaveArc L x a b := by
  rw [mem_leaveCode]
  constructor
  · rintro ⟨⟨u,c,s⟩,hm,⟨hu,hc⟩,he⟩
    refine ⟨⟨u,hu⟩,⟨c,hc⟩,s,hm,?_⟩
    apply (encoded_pair_eq L x a b _ _).mp
    rw [num_outer, num_output]
    exact he
  · rintro ⟨u,c,s,hm,rfl,rfl⟩
    refine ⟨(u.val,(c.val,s)),hm,⟨u.isLt,c.isLt⟩,?_⟩
    rw [num_outer, num_output]

theorem numbered_link (L : Code InputTy NatListTy) (x : InputTy.denote) (a b : V L x) :
    ((numbering L x).num a,(numbering L x).num b) ∈ (linksCode L).eval x ↔ LinkArc L x a b := by
  rw [mem_linksCode]
  constructor
  · rintro ⟨⟨⟨c,s⟩,⟨d,t⟩⟩,hm,⟨⟨hc,hd⟩,hne⟩,he⟩
    refine ⟨⟨c,hc⟩,⟨d,hd⟩,s,t,fun h => hne (congrArg Fin.val h),hm,?_⟩
    apply (encoded_pair_eq L x a b _ _).mp
    rw [num_output, num_input]
    exact he
  · rintro ⟨c,d,s,t,hne,hm,rfl,rfl⟩
    refine ⟨((c.val,s),(d.val,t)),hm,⟨⟨c.isLt,d.isLt⟩,fun h => hne (Fin.ext h)⟩,?_⟩
    rw [num_output, num_input]

end GridHardness.XorWireCode
