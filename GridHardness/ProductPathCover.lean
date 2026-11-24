/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoPathCover

/-!
# Product Path Cover

Disjoint indexed families of explicit path covers.
-/

@[expose] public section

namespace GridHardness.PathCover.Cover

/-- Place a separate path cover in each cell. Cell labels make disjointness
structural, including when different cells use different route choices. -/
def family {C I W : Type*} (covers : C → Cover I W) : Cover (C × I) (C × W) where
  size := fun ci => (covers ci.1).size ci.2
  equiv :=
    { toFun := fun ⟨⟨c, i⟩, j⟩ => (c, (covers c).equiv ⟨i, j⟩)
      invFun := fun ⟨c, w⟩ => ⟨(c, ((covers c).equiv.symm w).1),
        ((covers c).equiv.symm w).2⟩
      left_inv := by
        rintro ⟨⟨c, i⟩, j⟩
        exact congrArg (fun v : Blocks (covers c).size =>
          (⟨(c, v.1), v.2⟩ : Blocks (fun ci => (covers ci.1).size ci.2)))
          ((covers c).equiv.symm_apply_apply ⟨i, j⟩)
      right_inv := by
        rintro ⟨c, w⟩
        simp }

@[simp] theorem family_apply {C I W : Type*} (covers : C → Cover I W)
    (c : C) (i : I) (j : Fin ((covers c).size i + 1)) :
    (family covers).equiv ⟨(c, i), j⟩ = (c, (covers c).equiv ⟨i, j⟩) := rfl

@[simp] theorem family_first {C I W : Type*} (covers : C → Cover I W)
    (c : C) (i : I) : (family covers).first (c, i) = (c, (covers c).first i) := rfl

@[simp] theorem family_finish {C I W : Type*} (covers : C → Cover I W)
    (c : C) (i : I) : (family covers).finish (c, i) = (c, (covers c).finish i) := rfl

theorem family_internalEdges {C I W : Type*} (covers : C → Cover I W)
    (D : (C × W) → (C × W) → Prop)
    (hi : ∀ c, (covers c).InternalEdges (fun u v => D (c, u) (c, v))) :
    (family covers).InternalEdges D := by
  rintro ⟨c, i⟩ j
  exact hi c i j

end GridHardness.PathCover.Cover
