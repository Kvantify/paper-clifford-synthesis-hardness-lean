/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatXor

/-!
# XOR Routing

Use injectivity of a traversal to exclude closed components and recover a routing choice.
-/

public section

namespace GridHardness.XorGadget

/-- Injectivity alone supplies vertices outside each forbidden four-cycle:
there is no need to assume a vertex outside the whole eight-vertex gadget. -/
theorem noClosedComponent_of_injective {V : Type*} (next : V → V)
    (ho : OneOrbit next) (embed : Fin 8 → V) (he : Function.Injective embed)
    (b : Selection)
    (hs : ∀ e, b e = true → next (embed (arc e).1) = embed (arc e).2) :
    NoClosedComponent b := by
  have hne {i j : Fin 8} (h : i ≠ j) : embed i ≠ embed j := fun h' => h (he h')
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1, h6, h5⟩
    exact ho.not_closed_four (hs 0 h0) (hs 1 h1) (hs 6 h6) (hs 5 h5)
      (z := embed 2) ⟨hne (by decide), hne (by decide), hne (by decide), hne (by decide)⟩
  · rintro ⟨h2, h1, h7, h8⟩
    exact ho.not_closed_four (hs 2 h2) (hs 1 h1) (hs 7 h7) (hs 8 h8)
      (z := embed 0) ⟨hne (by decide), hne (by decide), hne (by decide), hne (by decide)⟩
  · rintro ⟨h3, h4, h9, h8⟩
    exact ho.not_closed_four (hs 3 h3) (hs 4 h4) (hs 9 h9) (hs 8 h8)
      (z := embed 0) ⟨hne (by decide), hne (by decide), hne (by decide), hne (by decide)⟩

theorem selection_of_oneOrbit_injective {V : Type*} (next : V → V)
    (ho : OneOrbit next) (embed : Fin 8 → V) (he : Function.Injective embed)
    (b : Selection) (hd : DegreeOK b)
    (hs : ∀ e, b e = true → next (embed (arc e).1) = embed (arc e).2) :
    b = leftRoute ∨ b = rightRoute :=
  (selection_iff b).mp ⟨hd, noClosedComponent_of_injective next ho embed he b hs⟩

end GridHardness.XorGadget
