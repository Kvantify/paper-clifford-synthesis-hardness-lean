/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleIsolation

/-!
# XOR Line Schedule Step

A concrete crossing step together with its next-step invariant.
Two marked XORs are replaced; all other marked XORs and the five new sections
are retained under explicit vertex embeddings.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule
open XorLine
variable {V I : Type*}

structure Family (D : V → V → Prop) (I : Type*) where
  embed : I → Fin 8 → V
  injective : Function.Injective (fun p : I × Fin 8 => embed p.1 p.2)
  isolated : ∀ i, XorIsolation D (embed i)

namespace Family
variable {D : V → V → Prop} (f : Family D I)

theorem embed_injective (i : I) : Function.Injective (f.embed i) := by
  intro j k h
  exact (Prod.mk.inj (f.injective h)).2

theorem distinct (i j : I) (h : i ≠j) (u v : Fin 8) : f.embed i u≠f.embed j v := by
  intro he
  exact h (Prod.mk.inj (f.injective he)).1

def crossSource (b : I) (i : Fin 4) : V := f.embed b (XorGadget.arc (Marked.crossArc i)).1
def crossTarget (b : I) (i : Fin 4) : V := f.embed b (XorGadget.arc (Marked.crossArc i)).2

theorem crossSource_injective (b : I) : Function.Injective (f.crossSource b) := by
  have h : Function.Injective (fun i : Fin 4 => (XorGadget.arc (Marked.crossArc i)).1) := by decide
  exact (f.embed_injective b).comp h

theorem cross_mandatory (b : I) :
    (∀ i, D (f.crossSource b i) (f.crossTarget b i)) ∧
    ∀ i v, D (f.crossSource b i) v → v=f.crossTarget b i := by
  constructor
  · intro i
    exact ((f.isolated b).internal _ _).mpr ⟨Marked.crossArc i,rfl⟩
  · intro i v hv
    have hc := Marked.crossArc_certificate i
    obtain ⟨j,rfl⟩ := (f.isolated b).outgoing _ hc.1 hc.2.1 v hv
    obtain ⟨e,he⟩ := ((f.isolated b).internal _ _).mp hv
    have hp := Prod.mk.inj he
    have he' := hc.2.2 e hp.1
    subst e
    exact congrArg (f.embed b) hp.2.symm

abbrev StepVertex (a : I) := Marked.ReplacementVertex (sourceMarker (n := 4) (f.embed a))

instance [Finite V] (a : I) : Finite (f.StepVertex a) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin 4)) := inferInstanceAs (Fintype (V ⊕ (Fin 4 × Bool)))
  exact inferInstanceAs (Finite (Marked.Outside (sourceMarker (n := 4) (f.embed a)) ⊕ XorLine.Vertex 4))

def step (a b : I) : f.StepVertex a → f.StepVertex a → Prop :=
  Marked.replacement (Subdivision.Adj D (f.crossSource b) (f.crossTarget b))
    (sourceMarker (f.embed a))

theorem step_correct [Finite V] (a b : I) (hab : a ≠b) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (f.step a b) := by
  have hm := f.cross_mandatory b
  have hs := sourceMarker_isolated D (f.embed a) (f.isolated a)
    (f.crossSource b) (f.crossTarget b)
    (fun i j => f.distinct a b hab j _) (fun i j => f.distinct a b hab j _)
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (Subdivision.Vertex V (Fin 4)) := inferInstanceAs (Fintype (V ⊕ (Fin 4 × Bool)))
  exact (Subdivision.hamiltonian_iff D (f.crossSource b) (f.crossTarget b)
    (f.crossSource_injective b) hm.1 hm.2).trans
    (Marked.replacement_correct _ _ (sourceMarker_injective _ (f.embed_injective a)) hs)

/-- Untouched labels plus the newly introduced five XOR sections. -/
abbrev NextIndex (a b : I) := {c : I // c≠a ∧ c≠b} ⊕ Fin 5

theorem survivor_disjoint (a c : I) (hca : c ≠a) (j : Fin 8) :
    (Sum.inl (f.embed c j) : Subdivision.Vertex V (Fin 4)) ∉
      Set.range (sourceMarker (n := 4) (f.embed a)) := by
  rintro ⟨k,hk⟩
  rcases k with l | p
  · exact f.distinct c a hca j l (Sum.inl.inj hk).symm
  · contradiction

def nextEmbed (a b : I) : NextIndex a b → Fin 8 → f.StepVertex a
  | .inl c, j => survivor (sourceMarker (f.embed a)) (Sum.inl ∘ f.embed c.val)
      (f.survivor_disjoint a c.val c.property.1) j
  | .inr i, j => .inr (x i j)

theorem nextEmbed_injective (a b : I) :
    Function.Injective (fun p : NextIndex a b × Fin 8 => f.nextEmbed a b p.1 p.2) := by
  rintro ⟨c,j⟩ ⟨d,k⟩ h
  rcases c with c | c <;> rcases d with d | d
  · have hh := congrArg Subtype.val (Sum.inl.inj h)
    change (Sum.inl (f.embed c.val j) : Subdivision.Vertex V (Fin 4)) =
      Sum.inl (f.embed d.val k) at hh
    have he : (c.val,j)=(d.val,k) := f.injective (Sum.inl.inj hh)
    obtain ⟨hc,hj⟩ := Prod.mk.inj he
    exact Prod.ext (congrArg Sum.inl (Subtype.ext hc)) hj
  · contradiction
  · contradiction
  · have he := Sum.inl.inj (Sum.inr.inj h)
    obtain ⟨hc,hj⟩ := Prod.mk.inj he
    exact Prod.ext (congrArg Sum.inr hc) hj

theorem nextEmbed_isolated (a b : I) (c : NextIndex a b) :
    XorIsolation (f.step a b) (f.nextEmbed a b c) := by
  rcases c with c | i
  · apply survivor_isolated
    apply subdivided_xor D (f.embed c.val) (f.isolated c.val)
    · exact fun i j => f.distinct c.val b c.property.2 j _
    · exact fun i j => f.distinct c.val b c.property.2 j _
  · exact section_isolated _ _ i

/-- The next iteration receives a concrete family of disjoint isolated XORs;
its isolation obligations have already been proved from the actual graph. -/
def next (a b : I) : Family (f.step a b) (NextIndex a b) where
  embed := f.nextEmbed a b
  injective := f.nextEmbed_injective a b
  isolated := f.nextEmbed_isolated a b

theorem step_vertex_count [Fintype V] (a : I) :
    Nat.card (f.StepVertex a)=Fintype.card V+40 := by
  letI : Fintype (Subdivision.Vertex V (Fin 4)) := inferInstanceAs (Fintype (V ⊕ (Fin 4 × Bool)))
  rw [Marked.replacement_vertex_count _ (sourceMarker_injective _ (f.embed_injective a))]
  rw [Subdivision.vertex_count]
  simp

end Family
end GridHardness.XorLineSchedule
