/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteTrim

/-!
# Lattice Route Trim Intersection

Trimming simple routes preserves endpoint-only intersections. An
original endpoint can survive only when the amount removed at that end
is zero; if it survives, it is still an endpoint of the trimmed route.
-/

public section

namespace GridHardness.LatticeRouteTrim
set_option autoImplicit false

variable {α : Type*}

/-- A surviving original first vertex forces zero trimming at the front. -/
theorem head_survives (a b : Nat) (l : List α) (hn : l.Nodup) (q : α)
    (hh : l.head? =some q) (hq : q ∈trim a b l) :
    a=0 ∧ (trim a b l).head?=some q := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hq
  rw [getElem] at he
  have hlen : a+b<l.length := by rw [length] at hi; omega
  rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at hh
  have hinj := List.nodup_iff_injective_getElem.mp hn
  have hidx := congrArg Fin.val
    (hinj (a₁ := ⟨a+i,by rw [length] at hi; omega⟩)
      (a₂ := ⟨0,by omega⟩) (he.trans (Option.some.inj hh).symm))
  have ha : a=0 := by change a+i=0 at hidx; omega
  refine ⟨ha,?_⟩
  subst a
  rw [head 0 b l hlen]
  exact hh

/-- A surviving original last vertex forces zero trimming at the back. -/
theorem last_survives (a b : Nat) (l : List α) (hn : l.Nodup) (q : α)
    (hl : l.getLast? =some q) (hq : q ∈trim a b l) :
    b=0 ∧ (trim a b l).getLast?=some q := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hq
  rw [getElem] at he
  have hlen : a+b<l.length := by rw [length] at hi; omega
  rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at hl
  have hinj := List.nodup_iff_injective_getElem.mp hn
  have hidx := congrArg Fin.val
    (hinj (a₁ := ⟨a+i,by rw [length] at hi; omega⟩)
      (a₂ := ⟨l.length-1,by omega⟩) (he.trans (Option.some.inj hl).symm))
  have hb : b=0 := by
    change a+i=l.length-1 at hidx
    rw [length] at hi
    omega
  refine ⟨hb,?_⟩
  subst b
  rw [getLast a 0 l hlen]
  exact hl

open LatticeRouteDirections (Point Endpoint)

/-- The original endpoint that survives identifies an end where no
vertices were removed. -/
theorem endpoint_survives_cases (a b : Nat) (l : List Point) (hn : l.Nodup)
    (q : Point) (he : Endpoint l q) (hq : q ∈trim a b l) :
    (l.head?=some q ∧ a=0) ∨ (l.getLast?=some q ∧ b=0) := by
  rcases he with he | he
  · exact Or.inl ⟨he,(head_survives a b l hn q he hq).1⟩
  · exact Or.inr ⟨he,(last_survives a b l hn q he hq).1⟩

/-- Any original endpoint remaining after trimming is still an endpoint. -/
theorem endpoint_survives (a b : Nat) (l : List Point) (hn : l.Nodup)
    (q : Point) (he : Endpoint l q) (hq : q ∈trim a b l) :
    Endpoint (trim a b l) q := by
  rcases he with he | he
  · exact Or.inl (head_survives a b l hn q he hq).2
  · exact Or.inr (last_survives a b l hn q he hq).2

/-- Removing arbitrary initial and terminal portions cannot turn an
endpoint-only intersection into an interior intersection. -/
theorem endpoint_intersection (a b c d : Nat) (l m : List Point)
    (hln : l.Nodup) (hmn : m.Nodup)
    (hinter : ∀ v, v ∈l → v ∈m → Endpoint l v ∧ Endpoint m v)
    (q : Point) (hql : q ∈trim a b l) (hqm : q ∈trim c d m) :
    Endpoint (trim a b l) q ∧ Endpoint (trim c d m) q := by
  obtain ⟨hl,hm⟩ := hinter q (mem a b l q hql) (mem c d m q hqm)
  exact ⟨endpoint_survives a b l hln q hl hql,
    endpoint_survives c d m hmn q hm hqm⟩

end GridHardness.LatticeRouteTrim
