/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleBundleTransport

/-!
# XOR Line Registry Basic

A registry separates untouched/current isolated XORs from the mandatory
bundles of lines that have already been inserted.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry
open XorLineSchedule

abbrev Slot := Fin 4 × Bool

def endpoint {V : Type*} {D : V → V → Prop} (b : Bundle D 4) (p : Slot) : V :=
  if p.2 then b.target p.1 else b.source p.1

@[simp] theorem endpoint_false {V : Type*} {D : V → V → Prop} (b : Bundle D 4) (i : Fin 4) :
    endpoint b (i,false)=b.source i := rfl
@[simp] theorem endpoint_true {V : Type*} {D : V → V → Prop} (b : Bundle D 4) (i : Fin 4) :
    endpoint b (i,true)=b.target i := rfl

structure Registry {V : Type*} (D : V → V → Prop) (X B : Type*) where
  xors : Family D X
  bundles : B → Bundle D 4
  bundle_injective : Function.Injective (fun p : B × Slot => endpoint (bundles p.1) p.2)
  disjoint : ∀ x b j p, xors.embed x j ≠ endpoint (bundles b) p

namespace Registry
variable {V X B : Type*} {D : V → V → Prop} (r : Registry D X B)

theorem sources_distinct (b c : B) (hbc : b ≠c) (i j : Fin 4) :
    (r.bundles b).source i≠(r.bundles c).source j := by
  intro h
  exact hbc (Prod.mk.inj (r.bundle_injective (a₁ := (b,(i,false))) (a₂ := (c,(j,false))) h)).1

theorem target_ne_endpoint (b c : B) (hbc : b ≠c) (i : Fin 4) (p : Slot) :
    (r.bundles b).target i ≠ endpoint (r.bundles c) p := by
  intro h
  exact hbc (Prod.mk.inj (r.bundle_injective (a₁ := (b,(i,true))) (a₂ := (c,p)) h)).1

theorem xor_ne_source (a : X) (b : B) (i : Fin 4) (j : Fin 8) :
    r.xors.embed a j≠(r.bundles b).source i := r.disjoint a b j (i,false)

theorem xor_ne_target (a : X) (b : B) (i : Fin 4) (j : Fin 8) :
    r.xors.embed a j≠(r.bundles b).target i := r.disjoint a b j (i,true)

end Registry

/-- The eight transverse-arc endpoints are exactly the eight XOR vertices. -/
def xorEndpoint (p : Slot) : Fin 8 :=
  if p.2 then (XorGadget.arc (XorLine.Marked.crossArc p.1)).2
  else (XorGadget.arc (XorLine.Marked.crossArc p.1)).1

theorem xorEndpoint_injective : Function.Injective xorEndpoint := by decide

theorem family_endpoint {V X : Type*} {D : V → V → Prop} (f : Family D X)
    (a : X) (p : Slot) : endpoint (f.bundle a) p=f.embed a (xorEndpoint p) := by
  rcases p with ⟨i,b⟩
  cases b <;> rfl

end GridHardness.XorLineRegistry
