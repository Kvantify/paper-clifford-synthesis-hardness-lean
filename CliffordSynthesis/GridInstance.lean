/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GridReduction
public import CliffordSynthesis.GridConnectivity
public import CliffordSynthesis.NoInstance

/-!
# Grid Instance

A total, computable instance map, using a constant no-instance for
disconnected grids, with polynomial bounds on qubits and threshold.
-/

@[expose] public section

namespace CliffordSynthesis.GridInstance

variable {m : Nat}

/-- A phase-free synthesis instance with a CNOT budget. -/
structure Instance where
  /-- Number of qubits on which the target acts. -/
  qubits : Nat
  /-- Target images of the Pauli generators. -/
  tableau : Circuit.Tableau qubits
  /-- The maximum number of CNOT gates allowed in a solution. -/
  threshold : Nat

def Accepts (a : Instance) : Prop := Circuit.SynthesizesWithin a.tableau a.threshold

def reduce (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) : Instance :=
  if GridConnectivity.connectedTest point then
    ⟨GridReduction.dimension point + (1 + EncodedTarget.recorderCount m),
      GridReduction.target point last, EncodedTarget.recorderCount m + m⟩
  else ⟨3, NoInstance.fanout, 1⟩

theorem hamiltonian_connected (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1))
    (p : (IntegerGrid.graph point).Walk 0 last) (hp : p.IsHamiltonian) :
    (IntegerGrid.graph point).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := IntegerGrid.graph point)).mpr
  exact ⟨0, fun v => ⟨p.takeUntil v (hp.mem_support v)⟩⟩

/-- The explicit instance map is correct for connected and disconnected
integer-grid inputs alike. Source vertices are distinct; endpoint zero is the
chosen start. No hardness or polynomial-time claim is assumed in this theorem. -/
theorem correct (point : Fin (m + 1) → Int × Int) (hp : Function.Injective point)
    (last : Fin (m + 1)) : Accepts (reduce point last) ↔
      ∃ p : (IntegerGrid.graph point).Walk 0 last, p.IsHamiltonian := by
  by_cases hc : GridConnectivity.connectedTest point = true
  · rw [reduce, ite_eq_left hc]
    exact GridReduction.synthesis_iff_hamiltonian point hp last
  · have hnc : ¬(IntegerGrid.graph point).Connected := by
      rwa [← GridConnectivity.connectedTest_correct]
    have hnp : ¬∃ p : (IntegerGrid.graph point).Walk 0 last, p.IsHamiltonian := by
      rintro ⟨p, h⟩
      exact hnc (hamiltonian_connected point last p h)
    rw [reduce, ite_eq_right hc]
    exact iff_of_false NoInstance.fanout_no_instance hnp

theorem qubit_bound (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) :
    (reduce point last).qubits ≤ max 3 (6 * m * m + 8 * m + 2) := by
  by_cases hc : GridConnectivity.connectedTest point = true
  · have hb := GridReduction.qubit_bound point (GridConnectivity.connectedTest_correct point |>.mp hc)
    simpa [reduce, hc] using hb.trans (le_max_right 3 _)
  · simp [reduce, hc]

theorem threshold_bound (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) :
    (reduce point last).threshold ≤ 6 * m * m + 8 * m + 1 := by
  by_cases hc : GridConnectivity.connectedTest point = true
  · simp [reduce, hc, GridReduction.threshold_eq]
  · simp [reduce, hc]

end CliffordSynthesis.GridInstance
