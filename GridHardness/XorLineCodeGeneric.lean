/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CrossoverCodeGeneric
public import GridHardness.XorLineReplacement

/-!
# XOR Line Code Generic

A polynomial compiler for attached directed gadgets with an input-sized
list of ports. Gadget vertices, internal arcs, and numbered port tables are
computed by `Code`; the generic correctness theorem checks their exact
interpretation rather than accepting an arbitrary function as a primitive.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorLineCode
open CliffordComplexity

abbrev NatListTy := Ty.list .nat
abbrev PairTy := Ty.pair .nat .nat
abbrev EdgesTy := Ty.list PairTy
/-- Outside graph, explicit row list, entering links, leaving links.
A boundary link is `(outside position, port number)`; list positions, not
labels, identify vertices and rows. -/
abbrev InputTy := Ty.pair GraphTy (.pair NatListTy (.pair EdgesTy EdgesTy))
abbrev TestTy := Ty.pair InputTy PairTy

def rows : Code InputTy NatListTy := .comp .snd .fst
def count : Code InputTy .nat := .comp .fst (.comp .fst .listLen)
def outsideEdges : Code InputTy EdgesTy := .comp .fst (.comp .snd .fst)
def enterLinks : Code InputTy EdgesTy := .comp .snd (.comp .snd .fst)
def leaveLinks : Code InputTy EdgesTy := .comp .snd (.comp .snd .snd)
def first : Code TestTy .nat := .comp .snd .fst
def second : Code TestTy .nat := .comp .snd .snd
def offset (a : Code TestTy .nat) : Code TestTy .nat :=
  .comp (.pair a (.comp .fst count)) .natSub

def anyEnv {σ τ : Ty} (test : Code (.pair σ τ) .bool) : Code (.pair σ (.list τ)) .bool :=
  .comp (Code.isNil (Code.filterEnv test)) .boolNot

theorem anyEnv_eval {σ τ : Ty} (test : Code (.pair σ τ) .bool)
    (x : σ.denote) (xs : List τ.denote) :
    (anyEnv test).eval (x,xs) = true ↔ ∃ a ∈ xs, test.eval (x,a) = true := by
  change (!(Code.isNil (Code.filterEnv test)).eval (x,xs)) = true ↔ _
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  have hn := isNil_eval_true (Code.filterEnv test) (x,xs)
  rw [filterEnv_eval] at hn
  exact (not_congr hn).trans (by simp only [List.filter_eq_nil_iff,not_forall,not_not,exists_prop])

/-- A port table contains `(port name, internal vertex number)` pairs. -/
def boundaryTest (links : Code InputTy EdgesTy) (outer inner : Code TestTy .nat) :
    Code (.pair TestTy PairTy) .bool :=
  Code.and
    (.comp (.pair (.pair (.comp .fst outer) (.comp .snd .fst))
      (.comp (.comp .fst .fst) links)) CrossoverCode.member)
    (.comp (.pair (.comp .fst (offset inner)) (.comp .snd .snd)) .natEq)

def boundary (links table : Code InputTy EdgesTy) (outer inner : Code TestTy .nat) : Code TestTy .bool :=
  .comp (.pair .id (.comp .fst table)) (anyEnv (boundaryTest links outer inner))

theorem boundary_eval (links table : Code InputTy EdgesTy) (outer inner : Code TestTy .nat)
    (x : InputTy.denote) (q : Nat × Nat) :
    (boundary links table outer inner).eval (x,q) = true ↔ ∃ p ∈ table.eval x,
      (outer.eval (x,q),p.1) ∈ links.eval x ∧ inner.eval (x,q)-x.1.1.length=p.2 := by
  change (anyEnv (boundaryTest links outer inner)).eval ((x,q),table.eval x) = true ↔ _
  rw [anyEnv_eval]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  change (CrossoverCode.member.eval ((outer.eval (x,q),p.1),links.eval x) &&
    decide (inner.eval (x,q)-x.1.1.length=p.2)) = true ↔ _
  rw [Bool.and_eq_true,CrossoverCode.member_eval,decide_eq_true_eq]

def adjacency (arcs input output : Code InputTy EdgesTy) : Code TestTy .bool :=
  .branch (.comp (.pair first (.comp .fst count)) Code.natLt)
    (.branch (.comp (.pair second (.comp .fst count)) Code.natLt)
      (.comp (.pair .snd (.comp .fst outsideEdges)) CrossoverCode.member)
      (boundary enterLinks input first second))
    (.branch (.comp (.pair second (.comp .fst count)) Code.natLt)
      (boundary leaveLinks output second first)
      (.comp (.pair (.pair (offset first) (offset second)) (.comp .fst arcs)) CrossoverCode.member))

theorem adjacency_eval (arcs input output : Code InputTy EdgesTy)
    (x : InputTy.denote) (q : Nat × Nat) :
    (adjacency arcs input output).eval (x,q) = true ↔
      if q.1 < x.1.1.length then
        if q.2 < x.1.1.length then q ∈ x.1.2.1
        else ∃ p ∈ input.eval x, (q.1,p.1) ∈ x.2.2.1 ∧ q.2-x.1.1.length=p.2
      else if q.2 < x.1.1.length then
        ∃ p ∈ output.eval x, (q.2,p.1) ∈ x.2.2.2 ∧ q.1-x.1.1.length=p.2
      else (q.1-x.1.1.length,q.2-x.1.1.length) ∈ arcs.eval x := by
  change (if Code.natLt.eval (q.1,x.1.1.length) then
    if Code.natLt.eval (q.2,x.1.1.length) then CrossoverCode.member.eval (q,x.1.2.1)
    else (boundary enterLinks input first second).eval (x,q)
    else if Code.natLt.eval (q.2,x.1.1.length) then
      (boundary leaveLinks output second first).eval (x,q)
    else CrossoverCode.member.eval ((q.1-x.1.1.length,q.2-x.1.1.length),arcs.eval x)) = true ↔ _
  rw [natLt_eval,natLt_eval]
  by_cases hu : q.1 < x.1.1.length <;> by_cases hv : q.2 < x.1.1.length
  · simpa only [hu,hv,decide_true,ite_true] using CrossoverCode.member_eval q x.1.2.1
  · simpa only [hu,hv,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,first,second,enterLinks,Code.eval]
      using boundary_eval enterLinks input first second x q
  · simpa only [hu,hv,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,first,second,leaveLinks,Code.eval]
      using boundary_eval leaveLinks output second first x q
  · simpa only [hu,hv,decide_false,Bool.false_eq_true,ite_false]
      using CrossoverCode.member_eval (q.1-x.1.1.length,q.2-x.1.1.length) (arcs.eval x)

def vertices (localVertices : Code InputTy NatListTy) : Code InputTy NatListTy :=
  Code.append (.comp .fst .fst) localVertices

def program (localVertices : Code InputTy NatListTy) (arcs input output : Code InputTy EdgesTy) :
    Code InputTy GraphTy :=
  .pair (vertices localVertices) (.pair
    (.comp (.pair .id (.comp (.pair (.comp (vertices localVertices) Code.indices)
      (.comp (vertices localVertices) Code.indices)) Code.cross))
      (Code.filterEnv (adjacency arcs input output))) (.const .nat 0))

theorem program_length (localVertices : Code InputTy NatListTy)
    (arcs input output : Code InputTy EdgesTy) (x : InputTy.denote) :
    ((program localVertices arcs input output).eval x).1.length =
      x.1.1.length + (localVertices.eval x).length := by
  change (x.1.1 ++ localVertices.eval x).length = _
  exact List.length_append

theorem program_arc_iff (localVertices : Code InputTy NatListTy)
    (arcs input output : Code InputTy EdgesTy) (x : InputTy.denote) (u v : Nat)
    (hu : u < x.1.1.length + (localVertices.eval x).length)
    (hv : v < x.1.1.length + (localVertices.eval x).length) :
    (u,v) ∈ ((program localVertices arcs input output).eval x).2.1 ↔
      (adjacency arcs input output).eval (x,(u,v)) = true := by
  change (u,v) ∈ (Code.filterEnv (adjacency arcs input output)).eval (x,
    Code.cross.eval ((Code.indices).eval ((vertices localVertices).eval x),
      (Code.indices).eval ((vertices localVertices).eval x))) ↔ _
  rw [filterEnv_eval]
  simp only [List.mem_filter,mem_cross_eval (σ := .nat) (τ := .nat),indices_eval]
  have hl : ((vertices localVertices).eval x).length = x.1.1.length+(localVertices.eval x).length :=
    List.length_append
  simp only [hl,List.mem_range,hu,hv,true_and]

def outside (x : InputTy.denote) (a b : Fin x.1.1.length) : Prop := (a.val,b.val) ∈ x.1.2.1

def enter {P : Type*} (pn : P → Nat) (x : InputTy.denote)
    (a : Fin x.1.1.length) (p : P) : Prop := (a.val,pn p) ∈ x.2.2.1

def leave {P : Type*} (pn : P → Nat) (x : InputTy.denote)
    (p : P) (a : Fin x.1.1.length) : Prop := (a.val,pn p) ∈ x.2.2.2

def numbering {G : Type*} (N : Numbering G) (x : InputTy.denote) :
    Numbering (Fin x.1.1.length ⊕ G) := (Numbering.fin x.1.1.length).sum N

section Adequacy
variable {G P : Type*} (N : Numbering G) (pn : P → Nat) (ports : List P)
variable (hports : ∀ p, p ∈ ports) (D : G → G → Prop) (inp out : P → G)
variable (localVertices : Code InputTy NatListTy) (arcs input output : Code InputTy EdgesTy)
variable (x : InputTy.denote)
variable (hsize : (localVertices.eval x).length = N.size)
variable (harcs : ∀ u v, (N.num u, N.num v) ∈ arcs.eval x ↔ D u v)
variable (hin : input.eval x = ports.map (fun p => (pn p, N.num (inp p))))
variable (hout : output.eval x = ports.map (fun p => (pn p, N.num (out p))))

include hports harcs hin hout in
theorem numbered_adjacency (a b : Fin x.1.1.length ⊕ G) :
    (adjacency arcs input output).eval (x,((numbering N x).num a,(numbering N x).num b)) = true ↔
      XorLineAttachment.Adj (outside x) D inp out (enter pn x) (leave pn x) a b := by
  rw [adjacency_eval]
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change (if a.val < x.1.1.length then if b.val < x.1.1.length then _ else _ else _) ↔ _
      rw [ite_eq_left a.isLt,ite_eq_left b.isLt]
      rfl
    | inr b =>
      change (if a.val < x.1.1.length then if x.1.1.length+N.num b < x.1.1.length then _ else _ else _) ↔ _
      rw [ite_eq_left a.isLt,ite_eq_right (by omega),hin]
      simp only [numbering,Numbering.sum_num_inl,Numbering.sum_num_inr,
        Numbering.fin_num,Numbering.fin_size,Nat.add_sub_cancel_left]
      change (∃ q ∈ ports.map (fun p => (pn p,N.num (inp p))),
        (a.val,q.1) ∈ x.2.2.1 ∧ N.num b=q.2) ↔
        ∃ p, (a.val,pn p) ∈ x.2.2.1 ∧ b=inp p
      constructor
      · rintro ⟨q,hq,hl,he⟩
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
        exact ⟨p,hl,N.num_inj he⟩
      · rintro ⟨p,hl,he⟩
        exact ⟨_,List.mem_map.mpr ⟨p,hports p,rfl⟩,hl,congrArg N.num he⟩
  | inr a =>
    cases b with
    | inl b =>
      change (if x.1.1.length+N.num a < x.1.1.length then _ else
        if b.val < x.1.1.length then _ else _) ↔ _
      rw [ite_eq_right (by omega),ite_eq_left b.isLt,hout]
      simp only [numbering,Numbering.sum_num_inl,Numbering.sum_num_inr,
        Numbering.fin_num,Numbering.fin_size,Nat.add_sub_cancel_left]
      change (∃ q ∈ ports.map (fun p => (pn p,N.num (out p))),
        (b.val,q.1) ∈ x.2.2.2 ∧ N.num a=q.2) ↔
        ∃ p, (b.val,pn p) ∈ x.2.2.2 ∧ a=out p
      constructor
      · rintro ⟨q,hq,hl,he⟩
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
        exact ⟨p,hl,N.num_inj he⟩
      · rintro ⟨p,hl,he⟩
        exact ⟨_,List.mem_map.mpr ⟨p,hports p,rfl⟩,hl,congrArg N.num he⟩
    | inr b =>
      change (if x.1.1.length+N.num a < x.1.1.length then _ else
        if x.1.1.length+N.num b < x.1.1.length then _ else _) ↔ _
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      simp only [numbering,Numbering.sum_num_inr,Numbering.fin_size,Nat.add_sub_cancel_left]
      exact harcs a b

noncomputable def decodeEquiv :
    (Fin x.1.1.length ⊕ G) ≃ Fin ((program localVertices arcs input output).eval x).1.length :=
  (numbering N x).equivFin.trans (finCongr ((program_length _ _ _ _ x).trans (congrArg (x.1.1.length+·) hsize)).symm)

include hports harcs hin hout in
theorem program_numbered_arc_iff (a b : Fin x.1.1.length ⊕ G) :
    ((decodeEquiv N localVertices arcs input output x hsize a).val,
      (decodeEquiv N localVertices arcs input output x hsize b).val) ∈
      ((program localVertices arcs input output).eval x).2.1 ↔
      XorLineAttachment.Adj (outside x) D inp out (enter pn x) (leave pn x) a b := by
  change ((numbering N x).num a,(numbering N x).num b) ∈ _ ↔ _
  rw [program_arc_iff _ _ _ _ _ _ _ (hsize ▸ (numbering N x).num_lt a)
    (hsize ▸ (numbering N x).num_lt b)]
  exact numbered_adjacency N pn ports hports D inp out arcs input output x harcs hin hout a b

include hports hsize harcs hin hout in
theorem program_correct (hN : 0 < N.size) :
    PathCover.Hamiltonian (XorLineAttachment.Adj (outside x) D inp out (enter pn x) (leave pn x)) ↔
      DirectedToBipartite.DIRECTED_HAMILTONIAN_CYCLE ((program localVertices arcs input output).eval x) := by
  have hn : 0 < ((program localVertices arcs input output).eval x).1.length := by
    rw [program_length,hsize]
    omega
  let e := decodeEquiv N localVertices arcs input output x hsize
  have he := program_numbered_arc_iff N pn ports hports D inp out localVertices arcs input output x hsize harcs hin hout
  constructor
  · rintro ⟨next,ho,ha⟩
    refine ⟨hn,e.symm.trans (next.trans e),?_,?_⟩
    · exact ho.transport e (by intro v; simp)
    · intro w
      obtain ⟨v,rfl⟩ := e.surjective w
      simpa only [Equiv.trans_apply,Equiv.symm_apply_apply] using (he v (next v)).mpr (ha v)
  · rintro ⟨_,next,ho,ha⟩
    refine ⟨e.trans (next.trans e.symm),?_,?_⟩
    · exact ho.transport e.symm (by intro v; simp)
    · intro v
      apply (he v _).mp
      simpa only [e,Equiv.trans_apply,Equiv.apply_symm_apply] using ha (e v)

end Adequacy
end GridHardness.XorLineCode
