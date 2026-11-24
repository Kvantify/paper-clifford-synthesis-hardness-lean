/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.LocalSubspace
public import CliffordSynthesis.Planes

/-!
# Local Chart

Pull the finite local table back from an arbitrary binary symplectic
space through a two-qubit chart. Chart linearity and preservation of the
symplectic form are proved from the four row vectors, not assumed.
-/

@[expose] public section

namespace CliffordSynthesis.LocalChart

open LinearMap (BilinForm)
open Planes (F plane SymplecticPair)

variable {V : Type*} [AddCommGroup V] [Module F V]

def bit (b : Bool) : F := if b then 1 else 0

theorem bit_xor (a b : Bool) : bit (a ^^ b) = bit a + bit b := by
  cases a <;> cases b <;> decide

private theorem bit_injective : Function.Injective bit := by decide

/-- Coordinates are x₁,x₂,z₁,z₂, matching Local.V. -/
def chart (a b c d : V) (q : Local.V) : V :=
  bit q.1 • a + bit q.2.1 • c + bit q.2.2.1 • b + bit q.2.2.2 • d

theorem chart_zero (a b c d : V) : chart a b c d 0 = 0 := by
  rw [show (0 : Local.V) = (false, false, false, false) by rfl]
  simp [chart, bit]

theorem chart_add (a b c d : V) (q r : Local.V) :
    chart a b c d (Local.add q r) = chart a b c d q + chart a b c d r := by
  simp only [chart, Local.add, bit_xor, add_smul]
  abel

/-- Two orthogonal symplectic qubit planes, with their displayed bases. -/
structure Frame (B : BilinForm F V) (a b c d : V) : Prop where
  first : SymplecticPair B a b
  second : SymplecticPair B c d
  ac : B a c = 0
  ad : B a d = 0
  bc : B b c = 0
  bd : B b d = 0
  ca : B c a = 0
  cb : B c b = 0
  da : B d a = 0
  db : B d b = 0

private theorem bit_sp : ∀ q r : Local.V,
    bit q.1 * bit r.2.2.1 + bit q.2.1 * bit r.2.2.2 +
    bit q.2.2.1 * bit r.1 + bit q.2.2.2 * bit r.2.1 = bit (Local.sp q r) := by decide

/-- The concrete chart preserves the symplectic form. -/
theorem chart_form (B : BilinForm F V) (a b c d : V)
    (h : Frame B a b c d) (q r : Local.V) :
    B (chart a b c d q) (chart a b c d r) = bit (Local.sp q r) := by
  simp only [chart, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, h.first.aa, h.first.ab, h.first.ba, h.first.bb,
    h.second.aa, h.second.ab, h.second.ba, h.second.bb,
    h.ac, h.ad, h.bc, h.bd, h.ca, h.cb, h.da, h.db,
    mul_zero, mul_one, zero_add, add_zero]
  rw [← bit_sp q r]
  ring

-- Kernel evaluation of the finite table needs extra recursion depth.
set_option maxRecDepth 100000 in
private theorem sp_separates : ∀ q r : Local.V,
    (∀ s : Local.V, Local.sp q s = Local.sp r s) → q = r := by decide

theorem chart_injective (B : BilinForm F V) (a b c d : V)
    (h : Frame B a b c d) : Function.Injective (chart a b c d) := by
  intro q r he
  apply sp_separates q r
  intro s
  apply bit_injective
  rw [← chart_form B a b c d h, he, chart_form B a b c d h]

/-- Restrict the actual ambient W to this joint two-qubit space. -/
noncomputable def pullback (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V) (h : Frame B a b c d) :
    Local.IsotropicSubspace := by
  classical
  refine {
    mem := fun q => decide (chart a b c d q ∈ W)
    zero_mem := ?_
    add_mem := ?_
    isotropic := ?_
  }
  · simp [chart_zero]
  · intro q r hq hr
    simp only [decide_eq_true_eq] at *
    rw [chart_add]
    exact W.add_mem hq hr
  · intro q r hq hr
    simp only [decide_eq_true_eq] at hq hr
    have hz := hW hr (chart a b c d q) hq
    rw [chart_form B a b c d h] at hz
    cases hs : Local.sp q r
    · rfl
    · simp [hs, bit] at hz

/-- The transition table for the restriction of an actual ambient isotropic W. -/
theorem ambient_localTable (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V) (h : Frame B a b c d) :
    Local.permitted (pullback B W hW a b c d h).signature = true :=
  Local.subspace_localTable _

/-- The row-addition part of the same table. -/
theorem ambient_rowAddition (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a b c d : V) (h : Frame B a b c d)
    (hs : (pullback B W hW a b c d h).signature = (2, 2, 1)) :
    Local.rowAddition (pullback B W hW a b c d h).before
      (pullback B W hW a b c d h).after = true :=
  Local.subspace_rowAddition _ hs

end CliffordSynthesis.LocalChart
