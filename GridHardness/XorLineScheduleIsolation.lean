/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineMarked
public import GridHardness.XorLineScheduleSubdivision

/-!
# XOR Line Schedule Isolation

Explicit isolation invariants for composing XOR-line moves.
The hypotheses concern actual incident edges, not Hamiltonian traversals.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule
open XorLine
variable {V : Type*}

structure XorIsolation (D : V → V → Prop) (e : Fin 8 → V) : Prop where
  internal : ∀ i j, D (e i) (e j) ↔ ∃ a : Fin 10, XorGadget.arc a=(i,j)
  outgoing : ∀ i, i≠0 → i≠7 → ∀ v, D (e i) v → ∃ j, v=e j
  incoming : ∀ j, j≠3 → j≠4 → ∀ v, D v (e j) → ∃ i, v=e i

/-- The unchanged identities of an XOR disjoint from all subdivided arcs. -/
theorem subdivided_xor {I : Type*} (D : V → V → Prop) (e : Fin 8 → V)
    (h : XorIsolation D e) (s t : I → V)
    (hs : ∀ i j, e j ≠s i) (ht : ∀ i j, e j ≠t i) :
    XorIsolation (Subdivision.Adj D s t) (Sum.inl ∘ e) := by
  constructor
  · intro i j
    change (D (e i) (e j) ∧ _) ↔ _
    constructor
    · exact fun hh => (h.internal i j).mp hh.1
    · intro hh
      refine ⟨(h.internal i j).mpr hh,?_⟩
      rintro ⟨k,hk,_⟩
      exact hs k i hk
  · intro i hi0 hi7 v hv
    rcases v with v | ⟨k,b⟩
    · obtain ⟨j,hj⟩ := h.outgoing i hi0 hi7 v hv.1
      exact ⟨j,congrArg Sum.inl hj⟩
    · exact False.elim (hs k i hv.1)
  · intro j hj3 hj4 v hv
    rcases v with v | ⟨k,b⟩
    · obtain ⟨i,hi⟩ := h.incoming j hj3 hj4 v hv.1
      exact ⟨i,congrArg Sum.inl hi⟩
    · exact False.elim (ht k j hv.2)

/-- The source marker after subdividing the arcs to be crossed. -/
def sourceMarker {n : Nat} (e : Fin 8 → V) : Source.Vertex n → Subdivision.Vertex V (Fin n)
  | .inl j => .inl (e j)
  | .inr p => .inr p

theorem sourceMarker_injective {n : Nat} (e : Fin 8 → V) (he : Function.Injective e) :
    Function.Injective (sourceMarker (n := n) e) := by
  rintro (i | p) (j | q) hh
  · exact congrArg Sum.inl (he (Sum.inl.inj hh))
  · contradiction
  · contradiction
  · exact congrArg Sum.inr (Sum.inr.inj hh)

/-- Isolation is discharged from the old XOR and the concrete fresh row pairs. -/
theorem sourceMarker_isolated {n : Nat} (D : V → V → Prop) (e : Fin 8 → V)
    (h : XorIsolation D e) (s t : Fin n → V)
    (hs : ∀ i j, e j ≠s i) (ht : ∀ i j, e j ≠t i) :
    Marked.Isolation (Subdivision.Adj D s t) (sourceMarker e) := by
  have hx := subdivided_xor D e h s t hs ht
  constructor
  · intro u v
    rcases u with j | ⟨i,b⟩ <;> rcases v with l | ⟨k,c⟩
    · exact hx.internal j l
    · cases c <;> simp [sourceMarker,Subdivision.Adj,Source.Adj,hs]
    · cases b <;> simp [sourceMarker,Subdivision.Adj,Source.Adj,ht]
    · cases b <;> cases c <;> simp [sourceMarker,Subdivision.Adj,Source.Adj]
  · intro u hu v hv
    rcases u with j | ⟨i,b⟩
    · obtain ⟨l,hl⟩ := hx.outgoing j (fun hj => hu (Or.inl hj))
        (fun hj => hu (Or.inr hj)) v hv
      exact ⟨.inl l,hl⟩
    · cases b
      · rcases v with v | ⟨k,c⟩
        · exact False.elim (Bool.false_ne_true hv.1)
        · obtain ⟨rfl,_,rfl⟩ := hv
          exact ⟨.inr (i,true),rfl⟩
      · exact False.elim (hu rfl)
  · intro v hv u hu
    rcases v with j | ⟨i,b⟩
    · obtain ⟨l,hl⟩ := hx.incoming j (fun hj => hv (Or.inl hj))
        (fun hj => hv (Or.inr hj)) u hu
      exact ⟨.inl l,hl⟩
    · cases b
      · exact False.elim (hv rfl)
      · rcases u with u | ⟨k,c⟩
        · exact Bool.noConfusion hu.2
        · obtain ⟨rfl,rfl,_⟩ := hu
          exact ⟨.inr (k,false),rfl⟩

/-- Old vertices outside the marked source survive with explicit identities. -/
def survivor {n : Nat} (mark : Source.Vertex n → V) (e : Fin 8 → V)
    (hd : ∀ i, e i ∉ Set.range mark) (i : Fin 8) : Marked.ReplacementVertex mark :=
  .inl ⟨e i,hd i⟩

theorem survivor_injective {n : Nat} (mark : Source.Vertex n → V) (e : Fin 8 → V)
    (hd : ∀ i, e i ∉ Set.range mark) (he : Function.Injective e) :
    Function.Injective (survivor mark e hd) := by
  intro i j hij
  exact he (congrArg Subtype.val (Sum.inl.inj hij))

/-- Refinement preserves every disjoint isolated XOR, even when its boundary
ports have edges to the replaced gadget. -/
theorem survivor_isolated {n : Nat} (D : V → V → Prop)
    (mark : Source.Vertex n → V) (e : Fin 8 → V)
    (hd : ∀ i, e i ∉ Set.range mark) (h : XorIsolation D e) :
    XorIsolation (Marked.replacement D mark) (survivor mark e hd) := by
  constructor
  · intro i j
    exact h.internal i j
  · intro i hi0 hi7 v hv
    rcases v with v | v
    · obtain ⟨j,hj⟩ := h.outgoing i hi0 hi7 v.val hv
      exact ⟨j,congrArg Sum.inl (Subtype.ext hj)⟩
    · obtain ⟨p,hp,_⟩ := hv
      obtain ⟨j,hj⟩ := h.outgoing i hi0 hi7 _ hp
      exact False.elim (hd j ⟨Source.inputPort n p,hj⟩)
  · intro j hj3 hj4 v hv
    rcases v with v | v
    · obtain ⟨i,hi⟩ := h.incoming j hj3 hj4 v.val hv
      exact ⟨i,congrArg Sum.inl (Subtype.ext hi)⟩
    · obtain ⟨p,hp,_⟩ := hv
      obtain ⟨i,hi⟩ := h.incoming j hj3 hj4 _ hp
      exact False.elim (hd i ⟨Source.outputPort n p,hi⟩)

/-- Every newly created section is again an isolated eight-vertex XOR. -/
theorem section_isolated {n : Nat} (D : V → V → Prop)
    (mark : Source.Vertex n → V) (i : Fin (n +1)) :
    XorIsolation (Marked.replacement D mark) (fun j => .inr (x i j)) := by
  constructor
  · intro j k
    change (i=i ∧ _) ↔ _
    exact and_iff_right rfl
  · intro j hj0 hj7 v hv
    rcases v with o | (⟨k,l⟩ | ⟨r,b⟩)
    · obtain ⟨p,_,hp⟩ := hv
      rcases p with c | r
      · cases c <;> simp [x,outputPort,hj0,hj7] at hp
      · simp [x,outputPort,row] at hp
    · obtain ⟨rfl,_⟩ := hv
      exact ⟨l,rfl⟩
    · cases b
      · exact False.elim hv
      · rcases hv with ⟨_,hh⟩ | ⟨_,hh⟩
        · exact False.elim (hj7 hh)
        · exact False.elim (hj0 hh)
  · intro j hj3 hj4 v hv
    rcases v with o | (⟨k,l⟩ | ⟨r,b⟩)
    · obtain ⟨p,_,hp⟩ := hv
      rcases p with c | r
      · cases c <;> simp [x,inputPort,hj3,hj4] at hp
      · simp [x,inputPort,row] at hp
    · obtain ⟨rfl,_⟩ := hv
      exact ⟨l,rfl⟩
    · cases b
      · rcases hv with ⟨_,hh⟩ | ⟨_,hh⟩
        · exact False.elim (hj4 hh)
        · exact False.elim (hj3 hh)
      · exact False.elim hv

end GridHardness.XorLineSchedule
