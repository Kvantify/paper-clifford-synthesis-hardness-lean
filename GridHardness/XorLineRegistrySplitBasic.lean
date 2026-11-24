/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistrySegments
public import GridHardness.XorLineRegistryCross

/-!
# XOR Line Registry Split Basic

Retain both geometric continuation bundles after a crossing. Their
sixteen endpoints are disjoint, including all fresh row vertices.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry.BundleSegments
open XorLineSchedule XorLine

/-- The two sides use complementary before/after choices for each arc. -/
def selected (which : Fin 4 → Bool) (s : Bool) (i : Fin 4) : Bool :=
  if s then which i else !which i

/-- `inl` names an original endpoint; `inr` names a fresh row endpoint. -/
def endpointTag (which : Fin 4 → Bool) (p : Bool × Slot) : Slot ⊕ Slot :=
  if selected which p.1 p.2.1 then
    if p.2.2 then .inl (p.2.1,true) else .inr (p.2.1,true)
  else if p.2.2 then .inr (p.2.1,false) else .inl (p.2.1,false)

theorem endpointTag_injective : ∀ which : Fin 4 → Bool,
    Function.Injective (endpointTag which) := by decide

variable {V : Type*} {D : V → V → Prop} (b : Bundle D 4) (e : Fin 8 → V)
variable (hs : ∀ i j, e j ≠b.source i) (ht : ∀ i j, e j ≠b.target i)

def oldEndpoint (p : Slot) : b.RefinedVertex e :=
  .inl ⟨.inl (endpoint b p),Bundle.old_not_in_sourceMarker e _ (by
    intro j
    rcases p with ⟨i,t⟩
    cases t
    · exact hs i j
    · exact ht i j)⟩

def tagVertex : Slot ⊕ Slot → b.RefinedVertex e
  | .inl p => oldEndpoint b e hs ht p
  | .inr p => .inr (row p.1 p.2)

theorem tagVertex_injective (hb : Function.Injective (endpoint b)) :
    Function.Injective (tagVertex b e hs ht) := by
  rintro (p | p) (q | q) h
  · have hh := congrArg Subtype.val (Sum.inl.inj h)
    exact congrArg Sum.inl (hb (Sum.inl.inj hh))
  · contradiction
  · contradiction
  · exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

theorem side_endpoint_tag (which : Fin 4 → Bool) (s : Bool) (p : Slot) :
    endpoint (side b e hs ht (selected which s)) p=
      tagVertex b e hs ht (endpointTag which (s,p)) := by
  rcases p with ⟨i,t⟩
  cases h : selected which s i <;> cases t <;>
    simp [endpoint,side,sideSource,sideTarget,endpointTag,h,tagVertex,oldEndpoint,
      beforeSource,beforeTarget,Bundle.afterSource,Bundle.afterTarget,row]

/-- Both continuation bundles jointly retain distinct endpoints. -/
theorem two_sides_injective (hb : Function.Injective (endpoint b)) (which : Fin 4 → Bool) :
    Function.Injective (fun p : Bool × Slot => endpoint (side b e hs ht (selected which p.1)) p.2) := by
  intro p q h
  change endpoint (side b e hs ht (selected which p.1)) p.2=
    endpoint (side b e hs ht (selected which q.1)) q.2 at h
  rw [side_endpoint_tag,side_endpoint_tag] at h
  exact endpointTag_injective which (tagVertex_injective b e hs ht hb h)

end GridHardness.XorLineRegistry.BundleSegments
