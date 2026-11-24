/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.ReplicatedTarget

/-!
# Encoded Target

The explicit target in the executable Boolean tableau semantics,
with canonical physical wire order and `6m+1` recorders per vertex.
-/

@[expose] public section

namespace CliffordSynthesis.EncodedTarget

open Planes (F)
open StandardSpace (standard fieldRows)
open Target (Wire)
open RecorderVectors (embed)

variable {d r n m : Nat}

def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

/-- Coordinates first, then the path wire, then the recorder wires. -/
def physicalLabel (d r : Nat) : Wire d r ≃ Fin (d + (1 + r)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr unitFin (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

theorem physical_order (w : Wire d r) : (physicalLabel d r w).val = Target.position w := by
  rcases w with w | (w | w) <;>
    simp [physicalLabel, unitFin, Target.position, Nat.add_assoc]

def bool (x : F) : Bool := decide (x = 1)

theorem bit_bool (x : F) : LocalChart.bit (bool x) = x := by
  have hx : x = 0 ∨ x = 1 := by exact (show ∀ x : F, x = 0 ∨ x = 1 by decide) x
  rcases hx with rfl | rfl <;> decide

/-- The exact rho(A) target: A on X rows and A inverse-transpose on Z rows. -/
def tableau (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Fin r → Fin d → F) : Circuit.Tableau n where
  x i p := if p.2 then false else bool (Target.matrix t X (label.symm i) (label.symm p.1))
  z i p := if p.2 then bool (Target.inverse t X (label.symm p.1) (label.symm i)) else false

theorem tableau_x (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Fin r → Fin d → F) (i : Fin n) :
    (fieldRows (tableau label t X)).x i = embed label (Target.matrix t X (label.symm i)) := by
  funext p
  rcases p with ⟨j, b⟩
  cases b
  · exact bit_bool _
  · rfl

theorem tableau_z (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Fin r → Fin d → F)
    (i j : Fin n) (b : Bool) :
    (fieldRows (tableau label t X)).z i (j, b) =
      if b then Target.inverse t X (label.symm j) (label.symm i) else 0 := by
  cases b
  · rfl
  · exact bit_bool _

/-- Pointwise synthesis equality supplies the final-row premise directly. -/
theorem same_target_rows (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Fin r → Fin d → F)
    (a : Circuit.Tableau n) (h : Circuit.Same a (tableau label t X)) :
    ∀ i, (fieldRows a).x i = embed label (Target.matrix t X (label.symm i)) := by
  intro i
  rw [← tableau_x label t X i]
  funext p
  exact congrArg LocalChart.bit (h i p).1

/-- A synthesis witness for the actual Boolean target yields a classical
implementation of its matrix with exactly the reduction's budget. -/
theorem synthesis_classical (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (t : Fin d → F)
    (h : Circuit.SynthesizesWithin (tableau label t (ReplicatedTarget.repeated vertex copies)) (r + m)) :
    ∃ cs : List (RowExtraction.AddGate n), cs.length = r + m ∧
      ∀ i, RowExtraction.runRows cs (standard n).x i =
        embed label (Target.matrix t (ReplicatedTarget.repeated vertex copies) (label.symm i)) := by
  obtain ⟨gs, hbudget, hsame⟩ := h
  exact ReplicatedTarget.target_classical label vertex hv hzero copies gs t
    (same_target_rows label t _ _ hsame) hbudget

/-- Recorders per vertex. The vertex type is `Fin (m + 1)`, giving
`6 (M - 1) + 1` copies for `M = m + 1` vertices. -/
def replication (m : Nat) : Nat := 6 * m + 1
def recorderCount (m : Nat) : Nat := (m + 1) * replication m

def copies (m : Nat) : Fin (recorderCount m) ≃ Fin (m + 1) × Fin (6 * m + 1) :=
  finProdFinEquiv.symm

/-- The complete, computable output instance for a cube vertex list and a
specified final vertex. Here m is one less than the number of vertices. -/
def instanceTableau (vertex : Fin (m + 1) → Fin d → F) (last : Fin (m + 1)) :
    Circuit.Tableau (d + (1 + recorderCount m)) :=
  tableau (physicalLabel d (recorderCount m)) (vertex last) (ReplicatedTarget.repeated vertex (copies m))

/-- The concrete Clifford-to-classical implication, without separate recorder,
visibility, saturation, freshness, or final-row assumptions. -/
theorem synthesis_to_row_circuit (vertex : Fin (m + 1) → Fin d → F)
    (hv : Function.Injective vertex) (hzero : vertex 0 = 0) (last : Fin (m + 1))
    (h : Circuit.SynthesizesWithin (instanceTableau vertex last) (recorderCount m + m)) :
    ∃ cs : List (RowExtraction.AddGate (d + (1 + recorderCount m))), cs.length = recorderCount m + m ∧
      ∀ i, RowExtraction.runRows cs (standard (d + (1 + recorderCount m))).x i =
        embed (physicalLabel d (recorderCount m))
          (Target.matrix (vertex last) (ReplicatedTarget.repeated vertex (copies m))
            ((physicalLabel d (recorderCount m)).symm i)) := by
  exact synthesis_classical (physicalLabel d (recorderCount m)) vertex hv hzero (copies m) (vertex last) h

end CliffordSynthesis.EncodedTarget
