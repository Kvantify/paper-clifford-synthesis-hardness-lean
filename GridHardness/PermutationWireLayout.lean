/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic

/-!
# Permutation Wire Layout

A bounded orthogonal centerline layout for a permutation of wires.
Each wire has two bends. Crossings are exactly inversions, no bend or endpoint
lies on another wire, and no three wires share a point. These are geometric
facts about centerlines, not an embedding of the gadget graph.
-/

@[expose] public section

namespace GridHardness.PermutationWireLayout

abbrev Point := Int × Int

section
variable {n : Nat} (p : Equiv.Perm (Fin n))

def low (i : Fin n) : Int := (i.val : Int) + 1
def high (i : Fin n) : Int := (n : Int) + 2 + (p i).val

def start (i : Fin n) : Point := ((n : Int) + 1, low i)
def upperBend (i : Fin n) : Point := (low i, low i)
def lowerBend (i : Fin n) : Point := (low i, high p i)
def finish (i : Fin n) : Point := (0, high p i)

/-- Three closed axis-aligned segments, directed from the right boundary to
the left boundary through a dedicated vertical column. -/
def OnWire (i : Fin n) (q : Point) : Prop :=
  (q.2 = low i ∧ low i ≤ q.1 ∧ q.1 ≤ (n : Int) + 1) ∨
  (q.1 = low i ∧ low i ≤ q.2 ∧ q.2 ≤ high p i) ∨
  (q.2 = high p i ∧ 0 ≤ q.1 ∧ q.1 ≤ low i)

instance (i : Fin n) (q : Point) : Decidable (OnWire p i q) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem low_bounds (i : Fin n) : 1 ≤ low i ∧ low i ≤ n := by
  have := i.isLt
  dsimp [low]
  omega

theorem high_bounds (i : Fin n) : (n : Int) + 2 ≤ high p i ∧ high p i ≤ 2*n+1 := by
  have := (p i).isLt
  dsimp [high]
  omega

theorem low_injective : Function.Injective (low : Fin n → Int) := by
  intro i j h
  apply Fin.ext
  dsimp [low] at h
  omega

theorem high_injective : Function.Injective (high p) := by
  intro i j h
  apply p.injective
  apply Fin.ext
  dsimp [high] at h
  omega

theorem low_lt_low {i j : Fin n} (h : i < j) : low i < low j := by
  dsimp [low]
  exact_mod_cast Nat.add_lt_add_right h 1

theorem high_lt_high {i j : Fin n} : high p i < high p j ↔ p i < p j := by
  dsimp [high]
  omega

theorem in_box (i : Fin n) (q : Point) (hq : OnWire p i q) :
    0 ≤ q.1 ∧ q.1 ≤ (n : Int)+1 ∧ 1 ≤ q.2 ∧ q.2 ≤ 2*n+1 := by
  have hl := low_bounds i
  have hh := high_bounds p i
  rcases hq with ⟨hy, hx, hx'⟩ | ⟨hx, hy, hy'⟩ | ⟨hy, hx, hx'⟩ <;> omega

/-- For columns in increasing order, there is exactly one crossing iff the
exit order is reversed. It is strictly inside the vertical and final segments. -/
theorem intersection_iff {i j : Fin n} (hij : i < j) (q : Point) :
    (OnWire p i q ∧ OnWire p j q) ↔
      (p j < p i ∧ q = (low i, high p j)) := by
  have hli := low_bounds i
  have hlj := low_bounds j
  have hhi := high_bounds p i
  have hhj := high_bounds p j
  have hl := low_lt_low hij
  have hh : high p i ≠ high p j := fun h => (ne_of_lt hij) (high_injective p h)
  constructor
  · rintro ⟨hi, hj⟩
    rcases hi with ⟨hiy, hix, hix'⟩ | ⟨hix, hiy, hiy'⟩ | ⟨hiy, hix, hix'⟩ <;>
      rcases hj with ⟨hjy, hjx, hjx'⟩ | ⟨hjx, hjy, hjy'⟩ | ⟨hjy, hjx, hjx'⟩
    all_goals first | omega | skip
    refine ⟨(high_lt_high p).mp (by omega), Prod.ext hix hjy⟩
  · rintro ⟨hp, rfl⟩
    have hh' := (high_lt_high p).mpr hp
    exact ⟨Or.inr (Or.inl ⟨rfl, by omega, by omega⟩),
      Or.inr (Or.inr ⟨rfl, by omega, by omega⟩)⟩

def crossing (i j : Fin n) : Point := (low i, high p j)

theorem crossing_injective : Function.Injective (fun ij : Fin n × Fin n => crossing p ij.1 ij.2) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  exact Prod.ext (low_injective (congrArg Prod.fst h))
    (high_injective p (congrArg Prod.snd h))

theorem crossing_strict {i j : Fin n} (hij : i < j) (hp : p j < p i) :
    low i < (crossing p i j).2 ∧ (crossing p i j).2 < high p i ∧
    0 < (crossing p i j).1 ∧ (crossing p i j).1 < low j := by
  have hl := low_bounds i
  have hh := high_bounds p j
  exact ⟨by dsimp [crossing]; omega, (high_lt_high p).mpr hp,
    by dsimp [crossing]; omega, low_lt_low hij⟩

/-- A crossing point is incident with exactly its two wires. -/
theorem no_third_wire {i j : Fin n} (hij : i < j) (hp : p j < p i)
    (k : Fin n) (hk : OnWire p k (crossing p i j)) : k = i ∨ k = j := by
  obtain ⟨hi, hj⟩ := (intersection_iff p hij (crossing p i j)).mpr ⟨hp, rfl⟩
  by_cases hki : k = i
  · exact Or.inl hki
  by_cases hkj : k = j
  · exact Or.inr hkj
  rcases lt_or_gt_of_ne hki with hlt | hgt
  · have hh := (intersection_iff p hlt _).mp ⟨hk, hi⟩
    have hh' : i = k := low_injective (congrArg Prod.fst hh.2)
    exact False.elim (hki hh'.symm)
  · have hh := (intersection_iff p hgt _).mp ⟨hi, hk⟩
    have hh' : j = k := high_injective p (congrArg Prod.snd hh.2)
    exact False.elim (hkj hh'.symm)

/-- All four endpoint/bend vertices belong to their own wire. -/
theorem vertices_on_wire (i : Fin n) :
    OnWire p i (start i) ∧ OnWire p i (upperBend i) ∧
    OnWire p i (lowerBend p i) ∧ OnWire p i (finish p i) := by
  have hl := low_bounds i
  have hh := high_bounds p i
  refine ⟨Or.inl ⟨rfl, ?_, le_rfl⟩, Or.inl ⟨rfl, le_rfl, ?_⟩,
    Or.inr (Or.inl ⟨rfl, ?_, le_rfl⟩), Or.inr (Or.inr ⟨rfl, le_rfl, ?_⟩)⟩ <;>
    dsimp [start, upperBend, lowerBend, finish] <;> omega

/-- No endpoint or bend of a wire lies on a different wire. -/
theorem vertices_clear (i j : Fin n) (hij : i ≠ j) (q : Point)
    (hq : q = start i ∨ q = upperBend i ∨ q = lowerBend p i ∨ q = finish p i) :
    ¬OnWire p j q := by
  intro hj
  have hv := vertices_on_wire p i
  have hi : OnWire p i q := by
    rcases hq with rfl | rfl | rfl | rfl
    · exact hv.1
    · exact hv.2.1
    · exact hv.2.2.1
    · exact hv.2.2.2
  have hli := low_bounds i
  have hlj := low_bounds j
  have hhi := high_bounds p i
  have hhj := high_bounds p j
  have hlo : low i ≠ low j := fun h => hij (low_injective h)
  have hhi' : high p i ≠ high p j := fun h => hij (high_injective p h)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨_, he⟩ := (intersection_iff p hlt q).mp ⟨hi, hj⟩
    rcases hq with rfl | rfl | rfl | rfl <;>
      have hx := congrArg Prod.fst he <;> have hy := congrArg Prod.snd he <;>
      dsimp [start, upperBend, lowerBend, finish] at hx hy <;> omega
  · obtain ⟨_, he⟩ := (intersection_iff p hgt q).mp ⟨hj, hi⟩
    rcases hq with rfl | rfl | rfl | rfl <;>
      have hx := congrArg Prod.fst he <;> have hy := congrArg Prod.snd he <;>
      dsimp [start, upperBend, lowerBend, finish] at hx hy <;> omega

/-- The marked crossings form a concrete quadratic-size set of index pairs. -/
def crossings : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ p ij.2 < p ij.1)

theorem crossing_count : (crossings p).card ≤ n*n := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

end
end GridHardness.PermutationWireLayout
