/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleStep

/-!
# XOR Line Schedule Bundle

Mandatory directed bundles remain available after a crossing.
The new bundle consists of the actual row-exit arcs into the old targets.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule
open XorLine
variable {V : Type*} {n : Nat}

structure Bundle (D : V → V → Prop) (n : Nat) where
  source : Fin n → V
  target : Fin n → V
  source_injective : Function.Injective source
  target_injective : Function.Injective target
  edge : ∀ i, D (source i) (target i)
  unique : ∀ i v, D (source i) v → v=target i

namespace Bundle
variable {D : V → V → Prop} (b : Bundle D n)

abbrev RefinedVertex (_b : Bundle D n) (e : Fin 8 → V) :=
  Marked.ReplacementVertex (sourceMarker (n := n) e)

instance [Finite V] (e : Fin 8 → V) : Finite (b.RefinedVertex e) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin n)) := inferInstanceAs (Fintype (V ⊕ (Fin n × Bool)))
  exact inferInstanceAs (Finite (Marked.Outside (sourceMarker (n := n) e) ⊕ XorLine.Vertex n))

def refined (e : Fin 8 → V) : b.RefinedVertex e → b.RefinedVertex e → Prop :=
  Marked.replacement (Subdivision.Adj D b.source b.target) (sourceMarker e)

theorem refined_correct [Finite V] (e : Fin 8 → V) (he : Function.Injective e)
    (hx : XorIsolation D e) (hs : ∀ i j, e j ≠ b.source i)
    (ht : ∀ i j, e j ≠ b.target i) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (b.refined e) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin n)) := inferInstanceAs (Fintype (V ⊕ (Fin n × Bool)))
  exact (Subdivision.hamiltonian_iff D b.source b.target b.source_injective b.edge b.unique).trans
    (Marked.replacement_correct _ _ (sourceMarker_injective e he)
      (sourceMarker_isolated D e hx b.source b.target hs ht))

theorem refined_vertex_count [Finite V] (e : Fin 8 → V) (he : Function.Injective e) :
    Nat.card (b.RefinedVertex e)=Nat.card V+10*n := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin n)) := inferInstanceAs (Fintype (V ⊕ (Fin n × Bool)))
  rw [Marked.replacement_vertex_count _ (sourceMarker_injective e he)]
  rw [Subdivision.vertex_count,Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin]
  omega

/-- The old targets are outside the removed XOR and the fresh row pairs. -/
theorem target_survives (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i) (i : Fin n) :
    (Sum.inl (b.target i) : Subdivision.Vertex V (Fin n)) ∉ Set.range (sourceMarker (n := n) e) := by
  rintro ⟨v,hv⟩
  rcases v with j | p
  · exact ht i j (Sum.inl.inj hv)
  · contradiction

def afterSource (e : Fin 8 → V) (i : Fin n) : b.RefinedVertex e := .inr (row i true)
def afterTarget (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i) (i : Fin n) : b.RefinedVertex e :=
  .inl ⟨.inl (b.target i),b.target_survives e ht i⟩

theorem afterSource_injective (e : Fin 8 → V) : Function.Injective (b.afterSource e) := by
  intro i j h
  simpa [afterSource,row] using h

theorem afterTarget_injective (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i) :
    Function.Injective (b.afterTarget e ht) := by
  intro i j h
  have hh := congrArg Subtype.val (Sum.inl.inj h)
  exact b.target_injective (Sum.inl.inj hh)

theorem after_edge (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i) (i : Fin n) :
    b.refined e (b.afterSource e i) (b.afterTarget e ht i) := by
  refine ⟨.inr i,?_,rfl⟩
  exact ⟨rfl,rfl⟩

/-- The residual row-exit arc has exactly one outgoing edge in the actual
refined graph. This is structural and does not assume a cycle exists. -/
theorem after_unique (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i)
    (i : Fin n) (v : b.RefinedVertex e) (hv : b.refined e (b.afterSource e i) v) :
    v=b.afterTarget e ht i := by
  rcases v with o | (⟨k,j⟩ | ⟨k,c⟩)
  · obtain ⟨p,hp,he⟩ := hv
    change outputPort n (.inr i)=outputPort n p at he
    have hep : p=.inr i := (outputPort_injective n he).symm
    subst p
    change Subdivision.Adj D b.source b.target (.inr (i,true)) o.val at hp
    apply congrArg Sum.inl
    apply Subtype.ext
    cases ho : o.val with
    | inl v =>
      rw [ho] at hp
      exact congrArg Sum.inl hp.2
    | inr q =>
      rw [ho] at hp
      exact Bool.noConfusion hp.2.1
  · exact False.elim hv
  · cases c <;> exact False.elim hv

/-- A crossed bundle can be used again, with fully explicit new endpoints. -/
def after (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i) : Bundle (b.refined e) n where
  source := b.afterSource e
  target := b.afterTarget e ht
  source_injective := b.afterSource_injective e
  target_injective := b.afterTarget_injective e ht
  edge := b.after_edge e ht
  unique := b.after_unique e ht

/-- All new XOR sections are disjoint from the residual bundle endpoints. -/
theorem section_disjoint_after (e : Fin 8 → V) (ht : ∀ i j, e j ≠ b.target i)
    (k : Fin (n + 1)) (i : Fin n) (j : Fin 8) :
    (Sum.inr (x k j) : b.RefinedVertex e) ≠ (b.after e ht).source i ∧
      (Sum.inr (x k j) : b.RefinedVertex e) ≠ (b.after e ht).target i := by
  constructor <;> intro h <;> cases h

/-- The same bundle can be crossed a second time by any newly created section;
all prerequisites for the second move follow from the first graph's edges. -/
theorem repeated_refinement_correct [Finite V] (e : Fin 8 → V)
    (he : Function.Injective e) (hx : XorIsolation D e)
    (hs : ∀ i j, e j ≠ b.source i) (ht : ∀ i j, e j ≠ b.target i)
    (k : Fin (n + 1)) :
    PathCover.Hamiltonian D ↔
      PathCover.Hamiltonian ((b.after e ht).refined (fun j => .inr (x k j))) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin n)) := inferInstanceAs (Fintype (V ⊕ (Fin n × Bool)))
  letI : Finite (b.RefinedVertex e) := inferInstanceAs
    (Finite (Marked.Outside (sourceMarker (n := n) e) ⊕ XorLine.Vertex n))
  exact (b.refined_correct e he hx hs ht).trans
    ((b.after e ht).refined_correct (fun j => .inr (x k j))
      (Sum.inr_injective.comp (x_injective k)) (section_isolated _ _ k)
      (fun i j => (b.section_disjoint_after e ht k i j).1)
      (fun i j => (b.section_disjoint_after e ht k i j).2))

end Bundle

namespace Family
variable {I : Type*} {D : V → V → Prop} (f : Family D I)

/-- Every original registered XOR supplies its four compulsory transverse arcs. -/
def bundle (i : I) : Bundle D 4 where
  source := f.crossSource i
  target := f.crossTarget i
  source_injective := f.crossSource_injective i
  target_injective := (f.embed_injective i).comp
    (by decide : Function.Injective (fun k : Fin 4 => (XorGadget.arc (Marked.crossArc k)).2))
  edge := (f.cross_mandatory i).1
  unique := (f.cross_mandatory i).2

theorem bundle_refined_eq (a b : I) : (f.bundle b).refined (f.embed a)=f.step a b := rfl

end Family
end GridHardness.XorLineSchedule
