/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Circuit
public import CliffordSynthesis.LocalChart

/-!
# Symplectic Circuit

Symplectic preservation of the actual H/S/CNOT gate semantics.
The row operations are stated over a general F₂ vector space.
-/

@[expose] public section

namespace CliffordSynthesis.SymplecticCircuit

open LinearMap (BilinForm)
open Planes (F)

variable {V : Type*} [AddCommGroup V] [Module F V]

@[ext] structure Rows (n : Nat) (V : Type*) where
  x : Fin n → V
  z : Fin n → V

variable {n : Nat}

structure IsSymplectic (B : BilinForm F V) (a : Rows n V) : Prop where
  xx : ∀ i j, B (a.x i) (a.x j) = 0
  xz : ∀ i j, B (a.x i) (a.z j) = if i = j then 1 else 0
  zx : ∀ i j, B (a.z i) (a.x j) = if i = j then 1 else 0
  zz : ∀ i j, B (a.z i) (a.z j) = 0

def H (q : Fin n) (a : Rows n V) : Rows n V where
  x i := if i = q then a.z i else a.x i
  z i := if i = q then a.x i else a.z i

def S (q : Fin n) (a : Rows n V) : Rows n V where
  x := a.x
  z i := if i = q then a.z i + a.x i else a.z i

def CX (c t : Fin n) (a : Rows n V) : Rows n V where
  x i := if i = t then a.x i + a.x c else a.x i
  z i := if i = c then a.z i + a.z t else a.z i

theorem H_symplectic (B : BilinForm F V) (a : Rows n V)
    (ha : IsSymplectic B a) (q : Fin n) : IsSymplectic B (H q a) := by
  constructor <;> intro i j <;>
    by_cases hi : i = q <;> by_cases hj : j = q <;>
    simp_all [H, ha.xx, ha.xz, ha.zx, ha.zz]
  all_goals solve_by_elim [Ne.symm]

theorem S_symplectic (B : BilinForm F V) (a : Rows n V)
    (ha : IsSymplectic B a) (q : Fin n) : IsSymplectic B (S q a) := by
  constructor <;> intro i j <;>
    by_cases hi : i = q <;> by_cases hj : j = q <;>
    simp_all [S, map_add, ha.xx, ha.xz, ha.zx, ha.zz]
  all_goals first | decide | solve_by_elim [Ne.symm]

theorem CX_symplectic (B : BilinForm F V) (a : Rows n V)
    (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t) :
    IsSymplectic B (CX c t a) := by
  constructor <;> intro i j <;>
    by_cases hic : i = c <;> by_cases hit : i = t <;>
    by_cases hjc : j = c <;> by_cases hjt : j = t <;>
    simp_all [CX, map_add, ha.xx, ha.xz, ha.zx, ha.zz]
  all_goals first | decide | solve_by_elim [Ne.symm]

/-- The two endpoints of every CNOT provide the frame required by LocalChart. -/
theorem endpoint_frame (B : BilinForm F V) (a : Rows n V)
    (ha : IsSymplectic B a) (c t : Fin n) (hct : c ≠ t) :
    LocalChart.Frame B (a.x c) (a.z c) (a.x t) (a.z t) := by
  constructor
  · constructor <;> simp [ha.xx, ha.xz, ha.zx, ha.zz]
  · constructor <;> simp [ha.xx, ha.xz, ha.zx, ha.zz]
  all_goals simp [ha.xx, ha.xz, ha.zx, ha.zz, hct, Ne.symm hct]

def applyGate (g : Circuit.Gate n) (a : Rows n V) : Rows n V :=
  Circuit.Gate.casesOn g (fun q => H q a) (fun q => S q a) (fun c t _ => CX c t a)

def run : List (Circuit.Gate n) → Rows n V → Rows n V
  | [], a => a
  | g :: gs, a => run gs (applyGate g a)

theorem gate_symplectic (B : BilinForm F V) (a : Rows n V)
    (ha : IsSymplectic B a) (g : Circuit.Gate n) :
    IsSymplectic B (applyGate g a) := by
  cases g with
  | H q => exact H_symplectic B a ha q
  | S q => exact S_symplectic B a ha q
  | CX c t hct => exact CX_symplectic B a ha c t hct

theorem run_symplectic (B : BilinForm F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (ha : IsSymplectic B a) : IsSymplectic B (run gs a) := by
  induction gs generalizing a with
  | nil => exact ha
  | cons g gs ih => exact ih _ (gate_symplectic B a ha g)

/-- Local transition table at any circuit prefix, on actual row vectors. -/
theorem prefix_localTable (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (a : Rows n V) (ha : IsSymplectic B a)
    (gs : List (Circuit.Gate n)) (c t : Fin n) (hct : c ≠ t) :
    Local.permitted (LocalChart.pullback B W hW
      ((run gs a).x c) ((run gs a).z c) ((run gs a).x t) ((run gs a).z t)
      (endpoint_frame B _ (run_symplectic B gs a ha) c t hct)).signature = true :=
  LocalChart.ambient_localTable B W hW _ _ _ _ _

end CliffordSynthesis.SymplecticCircuit
