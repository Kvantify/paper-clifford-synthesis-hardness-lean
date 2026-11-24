/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.AttachedGadget
public import GridHardness.DirectedToBipartiteCode
public import CliffordComplexity.Numbering

/-!
# Crossover Code Generic

Binary encodings and route programs for replacing a marked crossing edge.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.CrossoverCode
open CliffordComplexity

abbrev PairTy := Ty.pair .nat .nat
abbrev EdgesTy := Ty.list PairTy
/-- An outside graph and entering/leaving links. Both boundary lists store
`(outside position, 2*component + choice)`. Vertex labels and graph thresholds
have the same ignored status as in the directed Hamiltonian encoding. -/
abbrev InputTy := Ty.pair GraphTy (.pair EdgesTy EdgesTy)
abbrev TestTy := Ty.pair InputTy PairTy

def ports : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def portNumber (b s : Bool) : Nat := (Numbering.bool.prod Numbering.bool).num (b,s)

theorem mem_ports (p : Bool × Bool) : p ∈ ports := by rcases p with ⟨b,s⟩; cases b <;> cases s <;> decide

def pairEq : Code (.pair PairTy PairTy) .bool :=
  Code.and (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) .natEq)
    (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq)

theorem pairEq_eval (p q : Nat × Nat) : pairEq.eval (p,q) = decide (p = q) := by
  simp only [pairEq,Code.and,Code.eval,Prod.ext_iff,Bool.decide_and]
  rfl

def member : Code (.pair PairTy EdgesTy) .bool :=
  .comp (Code.isNil (Code.filterEnv pairEq)) .boolNot

theorem member_eval (p : Nat × Nat) (l : List (Nat × Nat)) :
    member.eval (p,l) = true ↔ p ∈ l := by
  have hf : (Code.filterEnv pairEq).eval (p,l) = l.filter (fun q => decide (p = q)) := by
    rw [filterEnv_eval pairEq p l]
    apply List.filter_congr
    intro q _
    exact pairEq_eval p q
  have he : (Code.filterEnv pairEq).eval (p,l) = [] ↔ p ∉ l := by
    rw [hf]
    simp only [List.filter_eq_nil_iff,decide_eq_true_eq]
    constructor
    · intro h hp
      exact h p hp rfl
    · intro h q hq he
      exact h (he.symm ▸ hq)
  have hn := (isNil_eval_true (Code.filterEnv pairEq) (p,l)).trans he
  change (!( (Code.isNil (Code.filterEnv pairEq)).eval (p,l))) = true ↔ _
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  exact (not_congr hn).trans not_not

/-- A finite table forms part of the program; it is not an input-sized numeric loop. -/
def anyTable {A : Type*} {σ : Ty} (xs : List A) (f : A → Code σ .bool) : Code σ .bool :=
  xs.foldr (fun a acc => Code.comp (Code.pair (f a) acc) Code.boolOr) (.const .bool false)

theorem anyTable_eval {A : Type*} {σ : Ty} (xs : List A) (f : A → Code σ .bool) (x : σ.denote) :
    (anyTable xs f).eval x = true ↔ ∃ a ∈ xs, (f a).eval x = true := by
  induction xs with
  | nil => simp [anyTable,Code.eval]
  | cons a xs ih =>
    change ((f a).eval x || (anyTable xs f).eval x) = true ↔ _
    rw [Bool.or_eq_true,ih]
    simp

def count : Code InputTy .nat := .comp .fst (.comp .fst .listLen)
def outsideEdges : Code InputTy EdgesTy := .comp .fst (.comp .snd .fst)
def enterLinks : Code InputTy EdgesTy := .comp .snd .fst
def leaveLinks : Code InputTy EdgesTy := .comp .snd .snd

def first : Code TestTy .nat := .comp .snd .fst
def second : Code TestTy .nat := .comp .snd .snd
def offset (a : Code TestTy .nat) : Code TestTy .nat :=
  .comp (.pair a (.comp .fst count)) .natSub

def boundary (links : Code InputTy EdgesTy) (outer inner : Code TestTy .nat)
    (port : Bool → Bool → Nat) : Code TestTy .bool :=
  anyTable ports (fun p => Code.and
    (.comp (.pair (.pair outer (.const .nat (portNumber p.1 p.2))) (.comp .fst links)) member)
    (.comp (.pair (offset inner) (.const .nat (port p.1 p.2))) .natEq))

theorem boundary_eval (links : Code InputTy EdgesTy) (outer inner : Code TestTy .nat)
    (port : Bool → Bool → Nat) (x : InputTy.denote) (q : Nat × Nat) :
    (boundary links outer inner port).eval (x,q) = true ↔ ∃ b s,
      (outer.eval (x,q),portNumber b s) ∈ links.eval x ∧
      inner.eval (x,q) - x.1.1.length = port b s := by
  rw [boundary,anyTable_eval]
  constructor
  · rintro ⟨⟨b,s⟩,_,h⟩
    change (member.eval ((outer.eval (x,q),portNumber b s),links.eval x) &&
      decide ((offset inner).eval (x,q) = port b s)) = true at h
    obtain ⟨hl,hi⟩ := Bool.and_eq_true_iff.mp h
    refine ⟨b,s,(member_eval _ _).mp hl,?_⟩
    exact of_decide_eq_true hi
  · rintro ⟨b,s,hl,hi⟩
    refine ⟨(b,s),mem_ports _,?_⟩
    change (member.eval ((outer.eval (x,q),portNumber b s),links.eval x) &&
      decide ((offset inner).eval (x,q) = port b s)) = true
    exact Bool.and_eq_true_iff.mpr ⟨(member_eval _ _).mpr hl,decide_eq_true hi⟩

def adjacency (arcs : List (Nat × Nat)) (input output : Bool → Bool → Nat) : Code TestTy .bool :=
  .branch (.comp (.pair first (.comp .fst count)) Code.natLt)
    (.branch (.comp (.pair second (.comp .fst count)) Code.natLt)
      (.comp (.pair .snd (.comp .fst outsideEdges)) member)
      (boundary enterLinks first second input))
    (.branch (.comp (.pair second (.comp .fst count)) Code.natLt)
      (boundary leaveLinks second first output)
      (.comp (.pair (.pair (offset first) (offset second)) (.const EdgesTy arcs)) member))

theorem adjacency_eval (arcs : List (Nat × Nat)) (input output : Bool → Bool → Nat)
    (x : InputTy.denote) (q : Nat × Nat) :
    (adjacency arcs input output).eval (x,q) = true ↔
      if q.1 < x.1.1.length then
        if q.2 < x.1.1.length then q ∈ x.1.2.1
        else ∃ b s, (q.1,portNumber b s) ∈ x.2.1 ∧ q.2-x.1.1.length = input b s
      else if q.2 < x.1.1.length then
        ∃ b s, (q.2,portNumber b s) ∈ x.2.2 ∧ q.1-x.1.1.length = output b s
      else (q.1-x.1.1.length,q.2-x.1.1.length) ∈ arcs := by
  change (if Code.natLt.eval (q.1,x.1.1.length) then
    if Code.natLt.eval (q.2,x.1.1.length) then member.eval (q,x.1.2.1)
    else (boundary enterLinks first second input).eval (x,q)
    else if Code.natLt.eval (q.2,x.1.1.length) then
      (boundary leaveLinks second first output).eval (x,q)
    else member.eval ((q.1-x.1.1.length,q.2-x.1.1.length),arcs)) = true ↔ _
  rw [natLt_eval,natLt_eval]
  by_cases hu : q.1 < x.1.1.length <;> by_cases hv : q.2 < x.1.1.length
  · simpa only [hu,hv,decide_true,ite_true] using member_eval q x.1.2.1
  · simpa only [hu,hv,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,first,second,enterLinks,leaveLinks,Code.eval]
      using boundary_eval enterLinks first second input x q
  · simpa only [hu,hv,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,first,second,enterLinks,leaveLinks,Code.eval]
      using boundary_eval leaveLinks second first output x q
  · simpa only [hu,hv,decide_false,Bool.false_eq_true,ite_false]
      using member_eval (q.1-x.1.1.length,q.2-x.1.1.length) arcs

def vertices (k : Nat) : Code InputTy (.list .nat) :=
  Code.append (.comp .fst .fst) (.const (.list .nat) (List.replicate k 0))

def program (k : Nat) (arcs : List (Nat × Nat)) (input output : Bool → Bool → Nat) :
    Code InputTy GraphTy :=
  .pair (vertices k) (.pair
    (.comp (.pair .id
      (.comp (.pair (.comp (vertices k) Code.indices) (.comp (vertices k) Code.indices)) Code.cross))
      (Code.filterEnv (adjacency arcs input output))) (.const .nat 0))

@[simp] theorem vertices_length (k : Nat) (x : InputTy.denote) :
    ((program k [] (fun _ _ => 0) (fun _ _ => 0)).eval x).1.length = x.1.1.length+k := by
  change (x.1.1 ++ List.replicate k 0).length = _
  simp

theorem program_length (k : Nat) (arcs : List (Nat × Nat)) (input output : Bool → Bool → Nat)
    (x : InputTy.denote) : ((program k arcs input output).eval x).1.length = x.1.1.length+k := by
  change (x.1.1 ++ List.replicate k 0).length = _
  simp

theorem program_arc_iff (k : Nat) (arcs : List (Nat × Nat)) (input output : Bool → Bool → Nat)
    (x : InputTy.denote) (u v : Nat) (hu : u < x.1.1.length + k) (hv : v < x.1.1.length + k) :
    (u,v) ∈ ((program k arcs input output).eval x).2.1 ↔
      (adjacency arcs input output).eval (x,(u,v)) = true := by
  change (u,v) ∈ (Code.filterEnv (adjacency arcs input output)).eval (x,
    Code.cross.eval ((Code.indices).eval ((vertices k).eval x),(Code.indices).eval ((vertices k).eval x))) ↔ _
  rw [filterEnv_eval]
  simp only [List.mem_filter,mem_cross_eval (σ := .nat) (τ := .nat),indices_eval]
  have hl : ((vertices k).eval x).length = x.1.1.length+k := by
    change (x.1.1 ++ List.replicate k 0).length = _
    simp
  simp only [hl,List.mem_range,hu,hv,true_and]

end GridHardness.CrossoverCode
