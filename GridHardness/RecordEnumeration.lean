/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic

/-!
# Record Enumeration

Lift a complete list of injectively encoded records back to their semantic
indices. The lift preserves the exact order and every duplicate; no finite-type
instance or independently chosen enumeration is needed.
-/

@[expose] public section

namespace GridHardness.RecordEnumeration
set_option autoImplicit false

variable {α β : Type*}

noncomputable def lift (rs : List β) (f : α →β)
    (h : ∀ r, r∈rs ↔ ∃ a, r=f a) : List α :=
  rs.attach.map (fun r => Classical.choose ((h r.val).mp r.property))

theorem lift_map (rs : List β) (f : α →β) (h : ∀ r, r∈rs ↔ ∃ a, r=f a) :
    (lift rs f h).map f=rs := by
  unfold lift
  rw [List.map_map]
  have he : (fun r : {r : β // r∈rs} => f (Classical.choose ((h r.val).mp r.property)))=
      Subtype.val := by
    funext r
    exact (Classical.choose_spec ((h r.val).mp r.property)).symm
  simp only [Function.comp_def]
  rw [he]
  simpa only [id_eq,List.map_id] using (List.attach_map_val (l:=rs) (f:=id))

theorem mem_lift (rs : List β) (f : α →β) (hf : Function.Injective f)
    (h : ∀ r, r∈rs ↔ ∃ a, r=f a) (a : α) : a∈lift rs f h ↔ f a∈rs := by
  constructor
  · intro ha
    have hm : f a∈(lift rs f h).map f := List.mem_map.mpr ⟨a,ha,rfl⟩
    rwa [lift_map] at hm
  · intro ha
    have hm : f a∈(lift rs f h).map f := by rw [lift_map]; exact ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    exact hf he ▸ hb

theorem lift_complete (rs : List β) (f : α →β) (hf : Function.Injective f)
    (h : ∀ r, r∈rs ↔ ∃ a, r=f a) (a : α) : a∈lift rs f h :=
  (mem_lift rs f hf h a).mpr ((h (f a)).mpr ⟨a,rfl⟩)

/-- A complete semantic enumeration with exactly the supplied record order. -/
theorem exists_lift (rs : List β) (f : α →β) (hf : Function.Injective f)
    (h : ∀ r, r∈rs ↔ ∃ a, r=f a) :
    ∃ xs : List α,xs.map f=rs ∧ ∀a,a∈xs :=
  ⟨lift rs f h,lift_map rs f h,lift_complete rs f hf h⟩

theorem lift_length (rs : List β) (f : α →β) (h : ∀ r, r∈rs ↔ ∃ a, r=f a) :
    (lift rs f h).length=rs.length := by
  have he := congrArg List.length (lift_map rs f h)
  simpa only [List.length_map] using he

end GridHardness.RecordEnumeration
