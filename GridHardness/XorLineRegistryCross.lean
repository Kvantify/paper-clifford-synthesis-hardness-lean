/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryBasic

/-!
# XOR Line Registry Cross

One insertion crossing, preserving all unprocessed XORs and all processed
bundles. The current line keeps the first newly created XOR section.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry.Registry
open XorLineSchedule XorLine
variable {V X B : Type*} {D : V → V → Prop} (r : Registry D X B)

abbrev CrossVertex (a : X) (b : B) := (r.bundles b).RefinedVertex (r.xors.embed a)
def crossAdj (a : X) (b : B) : r.CrossVertex a b → r.CrossVertex a b → Prop :=
  (r.bundles b).refined (r.xors.embed a)

theorem cross_correct [Finite V] (a : X) (b : B) :
    PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (r.crossAdj a b) :=
  (r.bundles b).refined_correct _ (r.xors.embed_injective a) (r.xors.isolated a)
    (r.xor_ne_source a b) (r.xor_ne_target a b)

theorem cross_vertex_count [Finite V] (a : X) (b : B) :
    Nat.card (r.CrossVertex a b)=Nat.card V+40 :=
  (r.bundles b).refined_vertex_count _ (r.xors.embed_injective a)

section
variable [DecidableEq X] [DecidableEq B]

def crossXor (a : X) (b : B) (c : X) (j : Fin 8) : r.CrossVertex a b :=
  if h : c=a then .inr (x 0 j) else
    survivor (sourceMarker (r.xors.embed a)) (Sum.inl ∘ r.xors.embed c)
      (r.xors.survivor_disjoint a c h) j

def crossBundle (a : X) (b c : B) : Bundle (r.crossAdj a b) 4 :=
  if h : c=b then (r.bundles b).after (r.xors.embed a) (r.xor_ne_target a b) else
    (r.bundles c).transport (r.bundles b) (r.xors.embed a)
      (r.sources_distinct c b h) (r.xor_ne_source a c) (r.xor_ne_target a c)

@[simp] theorem crossXor_self (a : X) (b : B) (j : Fin 8) :
    r.crossXor a b a j=.inr (x 0 j) := by simp [crossXor]

theorem crossXor_other (a c : X) (b : B) (h : c ≠ a) (j : Fin 8) :
    r.crossXor a b c j=.inl ⟨.inl (r.xors.embed c j),r.xors.survivor_disjoint a c h j⟩ := by
  simp [crossXor,h,survivor]

@[simp] theorem crossBundle_self_false (a : X) (b : B) (i : Fin 4) :
    endpoint (r.crossBundle a b b) (i,false)=.inr (row i true) := by
  simp [crossBundle,endpoint,Bundle.after,Bundle.afterSource]

@[simp] theorem crossBundle_self_true (a : X) (b : B) (i : Fin 4) :
    endpoint (r.crossBundle a b b) (i,true)=
      .inl ⟨.inl ((r.bundles b).target i),(r.bundles b).target_survives _ (r.xor_ne_target a b) i⟩ := by
  simp [crossBundle,endpoint,Bundle.after,Bundle.afterTarget]

theorem crossBundle_other (a : X) (b c : B) (h : c ≠ b) (p : Slot) :
    endpoint (r.crossBundle a b c) p=
      .inl ⟨.inl (endpoint (r.bundles c) p),
        Bundle.old_not_in_sourceMarker (r.xors.embed a) _ (fun j => r.disjoint a c j p)⟩ := by
  rcases p with ⟨i,k⟩
  cases k <;> simp [crossBundle,h,endpoint,Bundle.transport,Bundle.marked,Bundle.subdivided]

theorem crossXor_injective (a : X) (b : B) :
    Function.Injective (fun p : X × Fin 8 => r.crossXor a b p.1 p.2) := by
  rintro ⟨c,j⟩ ⟨d,k⟩ h
  change r.crossXor a b c j=r.crossXor a b d k at h
  by_cases hc : c=a <;> by_cases hd : d=a
  · subst c; subst d
    rw [crossXor_self,crossXor_self] at h
    have hj := (x_injective (0 : Fin 5)) (Sum.inr.inj h)
    exact Prod.ext rfl hj
  · subst c
    rw [crossXor_self,crossXor_other _ _ _ _ hd] at h
    contradiction
  · subst d
    rw [crossXor_other _ _ _ _ hc,crossXor_self] at h
    contradiction
  · rw [crossXor_other _ _ _ _ hc,crossXor_other _ _ _ _ hd] at h
    have hh := congrArg Subtype.val (Sum.inl.inj h)
    exact r.xors.injective (Sum.inl.inj hh)

theorem crossXor_isolated (a : X) (b : B) (c : X) :
    XorIsolation (r.crossAdj a b) (r.crossXor a b c) := by
  by_cases h : c=a
  · subst c
    have he : r.crossXor a b a=(fun j => .inr (x 0 j)) := funext (r.crossXor_self a b)
    rw [he]
    exact section_isolated _ _ 0
  · have he : r.crossXor a b c=survivor (sourceMarker (r.xors.embed a))
        (Sum.inl ∘ r.xors.embed c) (r.xors.survivor_disjoint a c h) := by
      funext j
      simp [crossXor,h]
    rw [he]
    apply survivor_isolated
    exact subdivided_xor D _ (r.xors.isolated c) _ _
      (r.xor_ne_source c b) (r.xor_ne_target c b)

theorem crossBundle_injective (a : X) (b : B) :
    Function.Injective (fun p : B × Slot => endpoint (r.crossBundle a b p.1) p.2) := by
  rintro ⟨c,i,s⟩ ⟨d,j,t⟩ h
  change endpoint (r.crossBundle a b c) (i,s)=endpoint (r.crossBundle a b d) (j,t) at h
  by_cases hc : c=b <;> by_cases hd : d=b
  · subst c; subst d
    cases s <;> cases t
    · simp only [crossBundle_self_false,Sum.inr.injEq,row,Prod.mk.injEq] at h
      exact Prod.ext rfl (Prod.ext h.1 rfl)
    · rw [crossBundle_self_false,crossBundle_self_true] at h
      contradiction
    · rw [crossBundle_self_true,crossBundle_self_false] at h
      contradiction
    · rw [crossBundle_self_true,crossBundle_self_true] at h
      have hh := congrArg Subtype.val (Sum.inl.inj h)
      exact Prod.ext rfl (Prod.ext ((r.bundles b).target_injective (Sum.inl.inj hh)) rfl)
  · subst c
    rw [crossBundle_other _ _ _ _ hd] at h
    cases s
    · rw [crossBundle_self_false] at h
      contradiction
    · rw [crossBundle_self_true] at h
      have hh := congrArg Subtype.val (Sum.inl.inj h)
      exact False.elim (r.target_ne_endpoint b d (Ne.symm hd) i (j,t) (Sum.inl.inj hh))
  · subst d
    rw [crossBundle_other _ _ _ _ hc] at h
    cases t
    · rw [crossBundle_self_false] at h
      contradiction
    · rw [crossBundle_self_true] at h
      have hh := congrArg Subtype.val (Sum.inl.inj h)
      exact False.elim (r.target_ne_endpoint b c (Ne.symm hc) j (i,s) (Sum.inl.inj hh).symm)
  · rw [crossBundle_other _ _ _ _ hc,crossBundle_other _ _ _ _ hd] at h
    have hh := congrArg Subtype.val (Sum.inl.inj h)
    exact r.bundle_injective (Sum.inl.inj hh)

theorem cross_disjoint (a : X) (b : B) (c : X) (d : B) (j : Fin 8) (p : Slot) :
    r.crossXor a b c j≠endpoint (r.crossBundle a b d) p := by
  intro h
  by_cases hc : c=a <;> by_cases hd : d=b
  · subst c; subst d
    rw [crossXor_self] at h
    rcases p with ⟨i,t⟩
    cases t
    · rw [crossBundle_self_false] at h
      cases h
    · rw [crossBundle_self_true] at h
      contradiction
  · subst c
    rw [crossXor_self,crossBundle_other _ _ _ _ hd] at h
    contradiction
  · subst d
    rw [crossXor_other _ _ _ _ hc] at h
    rcases p with ⟨i,t⟩
    cases t
    · rw [crossBundle_self_false] at h
      contradiction
    · rw [crossBundle_self_true] at h
      have hh := congrArg Subtype.val (Sum.inl.inj h)
      exact r.xor_ne_target c b i j (Sum.inl.inj hh)
  · rw [crossXor_other _ _ _ _ hc,crossBundle_other _ _ _ _ hd] at h
    have hh := congrArg Subtype.val (Sum.inl.inj h)
    exact r.disjoint c d j p (Sum.inl.inj hh)

/-- The graph operation keeps the label types: the current XOR is refreshed,
the crossed bundle is residual, and all other labels retain their old vertices. -/
def cross (a : X) (b : B) : Registry (r.crossAdj a b) X B where
  xors := ⟨r.crossXor a b,r.crossXor_injective a b,r.crossXor_isolated a b⟩
  bundles := r.crossBundle a b
  bundle_injective := r.crossBundle_injective a b
  disjoint := r.cross_disjoint a b

end
end GridHardness.XorLineRegistry.Registry
