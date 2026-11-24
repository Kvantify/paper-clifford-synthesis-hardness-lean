/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.SymplecticCircuit

/-!
# Standard Space

The canonical first-row Lagrangian and the Boolean circuit model.
No initial symplectic-tableau hypothesis is left to callers.
-/

@[expose] public section

namespace CliffordSynthesis.StandardSpace

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic)

abbrev Space (n : Nat) := Fin n × Bool → F

def coordinate {n : Nat} (p : Fin n × Bool) : Space n →ₗ[F] F := LinearMap.proj p

def form (n : Nat) : BilinForm F (Space n) :=
  ∑ i : Fin n, ((coordinate (i, false)).smulRight (coordinate (i, true)) +
    (coordinate (i, true)).smulRight (coordinate (i, false)))

theorem form_apply {n : Nat} (u v : Space n) :
    form n u v = ∑ i : Fin n, (u (i, false) * v (i, true) + u (i, true) * v (i, false)) := by
  simp [form, coordinate, LinearMap.sum_apply]

theorem form_symm (n : Nat) : (form n).IsSymm := by
  constructor
  intro u v
  simp only [form_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

def standard (n : Nat) : Rows n (Space n) where
  x i := Pi.single (i, false) 1
  z i := Pi.single (i, true) 1

theorem standard_symplectic (n : Nat) : IsSymplectic (form n) (standard n) := by
  constructor <;> intro i j <;>
    simp [form_apply, standard, Pi.single_apply, Prod.mk.injEq, eq_comm]

/-- Initial X-row space: all Z input coordinates are zero. -/
def initialW (n : Nat) : Submodule F (Space n) :=
  LinearMap.ker (LinearMap.pi (fun i : Fin n => LinearMap.proj (i, true)))

theorem initialW_mem {n : Nat} (v : Space n) :
    v ∈ initialW n ↔ ∀ i, v (i, true) = 0 := by
  simp [initialW, LinearMap.mem_ker, funext_iff]

theorem initialW_isotropic (n : Nat) : Splitting.Isotropic (form n) (initialW n) := by
  intro x hx y hy
  have hx' := (initialW_mem x).mp hx
  have hy' := (initialW_mem y).mp hy
  simp [form_apply, hx', hy']

theorem initialW_lagrangian (n : Nat) : (form n).orthogonal (initialW n) = initialW n := by
  apply le_antisymm
  · intro v hv
    rw [initialW_mem]
    intro i
    have hxi : (standard n).x i ∈ initialW n := by
      simp [initialW_mem, standard]
    have hzero := hv _ hxi
    simpa [form_apply, standard, Pi.single_apply, Prod.mk.injEq] using hzero
  · exact initialW_isotropic n

/-- Scalar embedding of the executable Boolean tableau semantics. -/
def fieldRows {n : Nat} (a : Circuit.Tableau n) : Rows n (Space n) where
  x i p := LocalChart.bit (a.x i p)
  z i p := LocalChart.bit (a.z i p)

theorem fieldRows_identity (n : Nat) : fieldRows (Circuit.identity n) = standard n := by
  ext i p
  all_goals rcases p with ⟨j, b⟩
  all_goals cases b <;> by_cases hij : i = j <;>
    simp [fieldRows, standard, Circuit.identity, LocalChart.bit,
      Prod.mk.injEq, hij]

theorem fieldRows_gate {n : Nat} (g : Circuit.Gate n) (a : Circuit.Tableau n) :
    fieldRows (Circuit.applyGate g a) = SymplecticCircuit.applyGate g (fieldRows a) := by
  cases g <;> ext i p <;>
    simp [fieldRows, Circuit.applyGate, Circuit.hadamard, Circuit.phase, Circuit.cnot,
      SymplecticCircuit.applyGate, SymplecticCircuit.H, SymplecticCircuit.S,
      SymplecticCircuit.CX, apply_ite, ite_apply, Pi.add_apply, LocalChart.bit_xor]
  all_goals split_ifs <;> simp_all

theorem fieldRows_run {n : Nat} (gs : List (Circuit.Gate n)) (a : Circuit.Tableau n) :
    fieldRows (Circuit.run gs a) = SymplecticCircuit.run gs (fieldRows a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp only [Circuit.run, SymplecticCircuit.run, ih, fieldRows_gate]

/-- Every actual circuit prefix is symplectic, starting from the actual identity. -/
theorem actual_run_symplectic {n : Nat} (gs : List (Circuit.Gate n)) :
    IsSymplectic (form n) (fieldRows (Circuit.run gs (Circuit.identity n))) := by
  rw [fieldRows_run, fieldRows_identity]
  exact SymplecticCircuit.run_symplectic _ gs _ (standard_symplectic n)

/-- The local table applies to the Boolean gate semantics. -/
theorem actual_localTable {n : Nat} (gs : List (Circuit.Gate n))
    (c t : Fin n) (hct : c ≠ t) :
    let a := fieldRows (Circuit.run gs (Circuit.identity n))
    Local.permitted (LocalChart.pullback (form n) (initialW n) (initialW_isotropic n)
      (a.x c) (a.z c) (a.x t) (a.z t)
      (SymplecticCircuit.endpoint_frame _ _ (actual_run_symplectic gs) c t hct)).signature = true := by
  exact LocalChart.ambient_localTable _ _ _ _ _ _ _ _

end CliffordSynthesis.StandardSpace
