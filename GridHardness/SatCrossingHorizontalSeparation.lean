/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalRouting

/-!
# SAT Crossing Horizontal Separation

Quantitative separation of the complete horizontal connection family.
Consecutive gaps in a row have disjoint horizontal ranges, and different
rows are separated by their permutation heights.
-/

@[expose] public section

namespace GridHardness.SatCrossingHorizontal
open CliffordSynthesis PermutationWireLayout
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem consecutive_columns_unique (i k a j : Fin n)
    (hk : ConsecutiveColumns p i k j) (ha : ConsecutiveColumns p i a j) : k=a :=
  le_antisymm (hk.2.2.2 a ha.2.1 ha.2.2.1) (ha.2.2.2 k hk.2.1 hk.2.2.1)

theorem consecutive_columns_order (i k a b j : Fin n)
    (hik : ConsecutiveColumns p i k j) (hab : ConsecutiveColumns p a b j)
    (hia : i ≠ a) : k ≤ a ∨ b ≤ i := by
  rcases lt_or_gt_of_ne hia with h | h
  · exact Or.inl (hik.2.2.2 a hab.1 h)
  · exact Or.inr (hab.2.2.2 i hik.1 h)

theorem different_connections_separated (i k j a b c : Fin n)
    (hik : ConsecutiveColumns p i k j) (hab : ConsecutiveColumns p a b c)
    (hd : (i, k, j) ≠(a, b, c)) (q t : Point)
    (hq : q ∈upperRoute p i k j ∨ q ∈lowerRoute p i k j)
    (ht : t ∈upperRoute p a b c ∨ t ∈lowerRoute p a b c) :
    110≤IntegerGrid.manhattan q t := by
  have hq' := route_bounds p i k j hik.2.2.1 q hq
  have ht' := route_bounds p a b c hab.2.2.1 t ht
  dsimp [IntegerGrid.manhattan]
  by_cases hj : j=c
  · subst c
    have hi : i≠a := by
      intro hi
      subst a
      have hk := consecutive_columns_unique p i k b j hik hab
      subst b
      exact hd rfl
    rcases consecutive_columns_order p i k a b j hik hab hi with h | h
    · have hh : low k≤low a := by dsimp [low]; omega
      omega
    · have hh : low b≤low i := by dsimp [low]; omega
      omega
  · have hh : high p j≠high p c := fun he => hj (high_injective p he)
    omega

/-- `true` selects the upper connector; `false` the oppositely directed
lower connector. This tag distinguishes the two edges of each connection. -/
def connectionRoute (i k j : Fin n) (side : Bool) : List Point :=
  if side then upperRoute p i k j else lowerRoute p i k j

theorem connectionRoute_mem (i k j : Fin n) (side : Bool) (q : Point)
    (hq : q ∈connectionRoute p i k j side) :
    q∈upperRoute p i k j ∨ q∈lowerRoute p i k j := by
  cases side
  · exact Or.inr hq
  · exact Or.inl hq

/-- All distinct horizontal edge routes are disjoint and cannot acquire
unintended unit-grid adjacencies. -/
theorem global_separation (i k j a b c : Fin n) (side other : Bool)
    (hik : ConsecutiveColumns p i k j) (hab : ConsecutiveColumns p a b c)
    (hd : (i, k, j, side) ≠(a, b, c, other)) (q t : Point)
    (hq : q ∈connectionRoute p i k j side) (ht : t ∈connectionRoute p a b c other) :
    8≤IntegerGrid.manhattan q t := by
  by_cases he : (i,k,j)=(a,b,c)
  · obtain ⟨rfl,h⟩ := Prod.mk.inj he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
    have hs : side≠other := by intro h; subst other; exact hd rfl
    cases side <;> cases other
    · exact False.elim (hs rfl)
    · have hh := pair_separated p i k j hik.2.2.1 t q ht hq
      dsimp [IntegerGrid.manhattan] at hh ⊢
      omega
    · exact pair_separated p i k j hik.2.2.1 q t hq ht
    · exact False.elim (hs rfl)
  · exact (by omega : 8≤110).trans
      (different_connections_separated p i k j a b c hik hab he q t
        (connectionRoute_mem p i k j side q hq) (connectionRoute_mem p a b c other t ht))

end GridHardness.SatCrossingHorizontal
