/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridProblems.Geometry
public import CliffordSynthesis.GridEmbedding
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Integer Grid

Finite induced integer-grid graphs and their bounding-rectangle normalization.
-/

@[expose] public section

namespace CliffordSynthesis.IntegerGrid

variable {m : Nat}

def lower (f : Fin (m + 1) → Int) : Int := Finset.univ.inf' Finset.univ_nonempty f
def upper (f : Fin (m + 1) → Int) : Int := Finset.univ.sup' Finset.univ_nonempty f
def span (f : Fin (m + 1) → Int) : Nat := (upper f - lower f).toNat
def shift (f : Fin (m + 1) → Int) (i : Fin (m + 1)) : Nat := (f i - lower f).toNat

theorem lower_le (f : Fin (m + 1) → Int) (i : Fin (m + 1)) : lower f ≤ f i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem le_upper (f : Fin (m + 1) → Int) (i : Fin (m + 1)) : f i ≤ upper f :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem shift_le_span (f : Fin (m + 1) → Int) (i : Fin (m + 1)) : shift f i ≤ span f := by
  have h := le_upper f i
  unfold shift span
  omega

theorem shift_distance (f : Fin (m + 1) → Int) (i j : Fin (m + 1)) :
    (shift f i - shift f j) + (shift f j - shift f i) = (f i - f j).natAbs := by
  have hi := lower_le f i
  have hj := lower_le f j
  unfold shift
  omega

theorem shift_injective_values (f : Fin (m + 1) → Int) (i j : Fin (m + 1))
    (h : shift f i = shift f j) : f i = f j := by
  have hi := lower_le f i
  have hj := lower_le f j
  unfold shift at h
  omega

def normalized (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) : Nat × Nat :=
  (shift (fun j => (point j).1) i, shift (fun j => (point j).2) i)

theorem normalized_bounds (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) :
    (normalized point i).1 ≤ span (fun j => (point j).1) ∧
    (normalized point i).2 ≤ span (fun j => (point j).2) :=
  ⟨shift_le_span (fun j => (point j).1) i, shift_le_span (fun j => (point j).2) i⟩

theorem normalized_distance (point : Fin (m + 1) → Int × Int) (i j : Fin (m + 1)) :
    hammingDist
      (GridEmbedding.encode (span (fun v => (point v).1)) (span (fun v => (point v).2)) (normalized point i))
      (GridEmbedding.encode (span (fun v => (point v).1)) (span (fun v => (point v).2)) (normalized point j)) =
      manhattan (point i) (point j) := by
  rw [GridEmbedding.encode_distance (normalized_bounds point i) (normalized_bounds point j)]
  exact congrArg₂ (· + ·) (shift_distance (fun v => (point v).1) i j)
    (shift_distance (fun v => (point v).2) i j)

theorem normalized_injective (point : Fin (m + 1) → Int × Int) (hp : Function.Injective point) :
    Function.Injective (normalized point) := by
  intro i j h
  apply hp
  exact Prod.ext (shift_injective_values (fun v => (point v).1) i j (congrArg Prod.fst h))
    (shift_injective_values (fun v => (point v).2) i j (congrArg Prod.snd h))

end CliffordSynthesis.IntegerGrid
