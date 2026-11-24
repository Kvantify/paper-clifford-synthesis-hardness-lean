/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.ListPrograms
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.OfFn

/-!
# Finite Record Lists

Explicit finite record lists for semantic compiler interfaces. Enumeration
is a semantic operation here; these lemmas do not assert its running cost.
-/

@[expose] public section

namespace GridHardness.FiniteRecordLists
open CliffordComplexity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

noncomputable def records {C : Type} [Fintype C] {σ : Ty} (f : C → σ.denote) :
    (Ty.list σ).denote := List.ofFn (fun i => f ((Fintype.equivFin C).symm i))

theorem length {C : Type} [Fintype C] {σ : Ty} (f : C → σ.denote) :
    (records f).length=Fintype.card C := List.length_ofFn

theorem mem {C : Type} [Fintype C] {σ : Ty} (f : C → σ.denote) (a : σ.denote) :
    a∈records f ↔ ∃ c,a=f c := by
  rw [records,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨(Fintype.equivFin C).symm i,hi.symm⟩
  · rintro ⟨c,rfl⟩
    exact ⟨(Fintype.equivFin C) c,by rw [Equiv.symm_apply_apply]⟩

end GridHardness.FiniteRecordLists
