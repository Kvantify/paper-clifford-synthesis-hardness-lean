/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistrySplitBasic

/-!
# XOR Line Registry Split

A crossing can replace one registered bundle by both complementary
continuations. This preserves the actual edge and disjointness invariants.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry.Registry
open XorLineSchedule XorLine BundleSegments
variable {V X B : Type*} {D : V → V → Prop} (r : Registry D X B)
variable [DecidableEq X] [DecidableEq B]

abbrev SplitIndex (b : B) := {c : B // c≠b} ⊕ Bool

def splitBundle (a : X) (b : B) (which : Fin 4 → Bool) : SplitIndex b → Bundle (r.crossAdj a b) 4
  | .inl c => r.crossBundle a b c.val
  | .inr s => side (r.bundles b) (r.xors.embed a)
      (r.xor_ne_source a b) (r.xor_ne_target a b) (selected which s)

theorem endpoint_injective (b : B) : Function.Injective (endpoint (r.bundles b)) := by
  intro p q h
  exact (Prod.mk.inj (r.bundle_injective (a₁ := (b,p)) (a₂ := (b,q)) h)).2

theorem split_side_ne_other (a : X) (b c : B) (hc : c ≠b) (which : Fin 4 → Bool)
    (s : Bool) (p q : Slot) :
    endpoint (side (r.bundles b) (r.xors.embed a)
      (r.xor_ne_source a b) (r.xor_ne_target a b) (selected which s)) p≠
      endpoint (r.crossBundle a b c) q := by
  intro h
  rw [side_endpoint_tag,crossBundle_other _ _ _ _ hc] at h
  cases he : endpointTag which (s,p) with
  | inl v =>
    rw [he] at h
    have hh := congrArg Subtype.val (Sum.inl.inj h)
    have hv : endpoint (r.bundles b) v=endpoint (r.bundles c) q := Sum.inl.inj hh
    have hz : (b,v)=(c,q) := r.bundle_injective hv
    exact hc (Prod.mk.inj hz).1.symm
  | inr v => rw [he] at h; cases h

theorem splitBundle_injective (a : X) (b : B) (which : Fin 4 → Bool) :
    Function.Injective (fun p : SplitIndex b × Slot => endpoint (r.splitBundle a b which p.1) p.2) := by
  rintro ⟨c,p⟩ ⟨d,q⟩ h
  change endpoint (r.splitBundle a b which c) p=endpoint (r.splitBundle a b which d) q at h
  cases c with
  | inl c =>
    cases d with
    | inl d =>
      have he : (c.val,p)=(d.val,q) := r.crossBundle_injective a b h
      obtain ⟨hc,hp⟩ := Prod.mk.inj he
      exact Prod.ext (congrArg Sum.inl (Subtype.ext hc)) hp
    | inr s => exact False.elim (r.split_side_ne_other a b c.val c.property which s q p h.symm)
  | inr s =>
    cases d with
    | inl d => exact False.elim (r.split_side_ne_other a b d.val d.property which s p q h)
    | inr t =>
      have he : (s,p)=(t,q) := two_sides_injective (r.bundles b) (r.xors.embed a)
        (r.xor_ne_source a b) (r.xor_ne_target a b) (r.endpoint_injective b) which h
      exact Prod.ext (congrArg Sum.inr (Prod.mk.inj he).1) (Prod.mk.inj he).2

theorem split_disjoint (a : X) (b : B) (which : Fin 4 → Bool)
    (c : X) (d : SplitIndex b) (j : Fin 8) (p : Slot) :
    r.crossXor a b c j≠endpoint (r.splitBundle a b which d) p := by
  cases d with
  | inl d => exact r.cross_disjoint a b c d.val j p
  | inr s =>
    change r.crossXor a b c j≠endpoint (side (r.bundles b) (r.xors.embed a)
      (r.xor_ne_source a b) (r.xor_ne_target a b) (selected which s)) p
    by_cases hc : c=a
    · subst c
      rw [crossXor_self]
      rcases p with ⟨i,t⟩
      have hh := section_disjoint_side (r.bundles b) (r.xors.embed a)
        (r.xor_ne_source a b) (r.xor_ne_target a b) (selected which s) 0 i j
      cases t
      · exact hh.1
      · exact hh.2
    · intro h
      rw [crossXor_other _ _ _ _ hc,side_endpoint_tag] at h
      cases he : endpointTag which (s,p) with
      | inl v =>
        rw [he] at h
        have hh := congrArg Subtype.val (Sum.inl.inj h)
        exact r.disjoint c b j v (Sum.inl.inj hh)
      | inr v => rw [he] at h; cases h

/-- Splitting retains both sides in the graph, with no assumed future edge
interface. `which` can account for the direction of each transverse arc. -/
def split (a : X) (b : B) (which : Fin 4 → Bool) : Registry (r.crossAdj a b) X (SplitIndex b) where
  xors := (r.cross a b).xors
  bundles := r.splitBundle a b which
  bundle_injective := r.splitBundle_injective a b which
  disjoint := r.split_disjoint a b which

end GridHardness.XorLineRegistry.Registry
