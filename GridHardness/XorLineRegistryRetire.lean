/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryCross

/-!
# XOR Line Registry Retire

Complete an inserted line: its current XOR becomes a processed mandatory
bundle, while the remaining original occurrences keep their isolation.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry
open XorLineSchedule

/-- Initially all occurrence XORs are unprocessed and there are no bundles. -/
def initial {V X : Type*} {D : V → V → Prop} (f : Family D X) : Registry D X Empty where
  xors := f
  bundles := Empty.elim
  bundle_injective := by rintro ⟨b,p⟩; exact b.elim
  disjoint := by intro x b; exact b.elim

namespace Registry
variable {V B : Type*} {D : V → V → Prop} {n : Nat}
variable (r : Registry D (Fin (n +1)) B)

def retireBundle : Option B → Bundle D 4
  | none => r.xors.bundle 0
  | some b => r.bundles b

theorem retireBundle_injective :
    Function.Injective (fun p : Option B × Slot => endpoint (r.retireBundle p.1) p.2) := by
  rintro ⟨c,p⟩ ⟨d,q⟩ h
  change endpoint (r.retireBundle c) p=endpoint (r.retireBundle d) q at h
  cases c with
  | none =>
    cases d with
    | none =>
      change endpoint (r.xors.bundle 0) p=endpoint (r.xors.bundle 0) q at h
      rw [family_endpoint,family_endpoint] at h
      exact Prod.ext rfl (xorEndpoint_injective (r.xors.embed_injective 0 h))
    | some d =>
      change endpoint (r.xors.bundle 0) p=endpoint (r.bundles d) q at h
      rw [family_endpoint] at h
      exact False.elim (r.disjoint 0 d (xorEndpoint p) q h)
  | some c =>
    cases d with
    | none =>
      change endpoint (r.bundles c) p=endpoint (r.xors.bundle 0) q at h
      rw [family_endpoint] at h
      exact False.elim (r.disjoint 0 c (xorEndpoint q) p h.symm)
    | some d =>
      change endpoint (r.bundles c) p=endpoint (r.bundles d) q at h
      have he : (c,p)=(d,q) := r.bundle_injective h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      rfl

def retire : Registry D (Fin n) (Option B) where
  xors := {
    embed := fun i => r.xors.embed i.succ
    injective := by
      rintro ⟨i,j⟩ ⟨k,l⟩ h
      have he : (i.succ,j)=(k.succ,l) := r.xors.injective h
      exact Prod.ext (Fin.succ_inj.mp (Prod.mk.inj he).1) (Prod.mk.inj he).2
    isolated := fun i => r.xors.isolated i.succ }
  bundles := r.retireBundle
  bundle_injective := r.retireBundle_injective
  disjoint := by
    intro i b j p
    cases b with
    | none =>
      change r.xors.embed i.succ j≠endpoint (r.xors.bundle 0) p
      rw [family_endpoint]
      exact r.xors.distinct i.succ 0 (Fin.succ_ne_zero i) j _
    | some b => exact r.disjoint i.succ b j p

end Registry
end GridHardness.XorLineRegistry
