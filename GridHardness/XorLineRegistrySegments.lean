/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryBasic

/-!
# XOR Line Registry Segments

Both sides of a crossed compulsory arc remain available. Selecting a side
separately for each directed arc permits geometrically coherent continuation
bundles even though the transverse arcs alternate direction.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry
open XorLineSchedule XorLine
namespace BundleSegments
variable {V : Type*} {D : V → V → Prop} (b : Bundle D 4) (e : Fin 8 → V)

/-- Before refinement, the old source has exactly the first subdivision edge. -/
theorem subdivided_source_unique (i : Fin 4) (v : Subdivision.Vertex V (Fin 4))
    (hv : Subdivision.Adj D b.source b.target (.inl (b.source i)) v) :
    v=.inr (i,false) := by
  rcases v with v | ⟨j,s⟩
  · have ht := b.unique i v hv.1
    exact False.elim (hv.2 ⟨i,rfl,ht⟩)
  · have hij := b.source_injective hv.1
    obtain rfl := hij
    obtain rfl := hv.2
    rfl

def beforeSource (hs : ∀ i j, e j ≠b.source i) (i : Fin 4) : b.RefinedVertex e :=
  .inl ⟨.inl (b.source i),Bundle.old_not_in_sourceMarker e _ (hs i)⟩
def beforeTarget (i : Fin 4) : b.RefinedVertex e := .inr (row i false)

theorem before_edge (hs : ∀ i j, e j ≠b.source i) (i : Fin 4) :
    b.refined e (beforeSource b e hs i) (beforeTarget b e i) := by
  refine ⟨.inr i,?_,rfl⟩
  exact ⟨rfl,rfl⟩

theorem before_unique (hs : ∀ i j, e j ≠b.source i) (i : Fin 4)
    (v : b.RefinedVertex e) (hv : b.refined e (beforeSource b e hs i) v) :
    v=beforeTarget b e i := by
  cases v with
  | inl o =>
    have ho := subdivided_source_unique b i o.val hv
    exact False.elim (o.property ⟨.inr (i,false),ho.symm⟩)
  | inr v =>
    obtain ⟨p,hp,he⟩ := hv
    have hp' := subdivided_source_unique b i _ hp
    cases p with
    | inl s => cases s <;> cases hp'
    | inr j =>
      have hij : j=i := (Prod.mk.inj (Sum.inr.inj hp')).1
      subst j
      exact congrArg Sum.inr he

/-- The incoming residual segments are actual mandatory arcs too. -/
def before (hs : ∀ i j, e j ≠b.source i) : Bundle (b.refined e) 4 where
  source := beforeSource b e hs
  target := beforeTarget b e
  source_injective := by
    intro i j h
    have hh := congrArg Subtype.val (Sum.inl.inj h)
    exact b.source_injective (Sum.inl.inj hh)
  target_injective := by
    intro i j h
    simpa [beforeTarget,row] using h
  edge := before_edge b e hs
  unique := before_unique b e hs

/-- `true` selects the segment after the row, `false` the one before it. -/
def sideSource (hs : ∀ i j, e j ≠b.source i) (side : Fin 4 → Bool) (i : Fin 4) : b.RefinedVertex e :=
  if side i then b.afterSource e i else beforeSource b e hs i

def sideTarget (ht : ∀ i j, e j ≠b.target i) (side : Fin 4 → Bool) (i : Fin 4) : b.RefinedVertex e :=
  if side i then b.afterTarget e ht i else beforeTarget b e i

theorem sideSource_injective (hs : ∀ i j, e j ≠b.source i) (side : Fin 4 → Bool) :
    Function.Injective (sideSource b e hs side) := by
  intro i j h
  unfold sideSource at h
  split at h <;> split at h
  · exact b.afterSource_injective e h
  · contradiction
  · contradiction
  · exact (before b e hs).source_injective h

theorem sideTarget_injective (ht : ∀ i j, e j ≠b.target i) (side : Fin 4 → Bool) :
    Function.Injective (sideTarget b e ht side) := by
  intro i j h
  unfold sideTarget at h
  split at h <;> split at h
  · exact b.afterTarget_injective e ht h
  · contradiction
  · contradiction
  · simpa [beforeTarget,row] using h

/-- A mixed continuation bundle, chosen per arc direction. Every edge and
unique-outgoing fact is inherited from the actual refined graph. -/
def side (hs : ∀ i j, e j ≠b.source i) (ht : ∀ i j, e j ≠b.target i)
    (which : Fin 4 → Bool) : Bundle (b.refined e) 4 where
  source := sideSource b e hs which
  target := sideTarget b e ht which
  source_injective := sideSource_injective b e hs which
  target_injective := sideTarget_injective b e ht which
  edge := by
    intro i
    by_cases h : which i=true
    · simpa [sideSource,sideTarget,h] using b.after_edge e ht i
    · have hh : which i=false := Bool.eq_false_iff.mpr h
      simpa [sideSource,sideTarget,hh] using before_edge b e hs i
  unique := by
    intro i v hv
    by_cases h : which i=true
    · simp only [sideSource,h,Bool.true_eq,ite_true] at hv
      simpa [sideTarget,h] using b.after_unique e ht i v hv
    · have hh : which i=false := Bool.eq_false_iff.mpr h
      simp only [sideSource,hh,Bool.false_eq_true,ite_false] at hv
      simpa [sideTarget,hh] using before_unique b e hs i v hv

/-- All new isolated sections are disjoint from either choice of residual side. -/
theorem section_disjoint_side (hs : ∀ i j, e j ≠b.source i) (ht : ∀ i j, e j ≠b.target i)
    (which : Fin 4 → Bool) (k : Fin 5) (i : Fin 4) (j : Fin 8) :
    (Sum.inr (x k j) : b.RefinedVertex e)≠(side b e hs ht which).source i ∧
      (Sum.inr (x k j) : b.RefinedVertex e)≠(side b e hs ht which).target i := by
  by_cases h : which i=true
  · simp only [side,sideSource,sideTarget,h,Bool.true_eq,ite_true]
    exact b.section_disjoint_after e ht k i j
  · have hh : which i=false := Bool.eq_false_iff.mpr h
    simp only [side,sideSource,sideTarget,hh,Bool.false_eq_true,ite_false]
    constructor <;> intro he <;> cases he

/-- The top-to-bottom transverse arcs alternate direction between the two
original endpoints, so geometric side selection must alternate too. -/
def towardTrue : Fin 4 → Bool := ![true,false,true,false]
def towardFalse (i : Fin 4) : Bool := !towardTrue i

theorem direction_certificate : ∀ i : Fin 4,
    (towardTrue i=true ↔ (XorGadget.arc (Marked.crossArc i)).2<4) ∧
    towardFalse i≠towardTrue i := by decide

end BundleSegments
end GridHardness.XorLineRegistry
