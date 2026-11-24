/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.IntegerGrid

/-!
# Grid Connectivity

A finite reachability computation, with one round per source vertex,
used to avoid expanding the bounding rectangle of disconnected inputs.
-/

@[expose] public section

namespace CliffordSynthesis.GridConnectivity

variable {m : Nat}

def reached (point : Fin (m + 1) → Int × Int) (s : Fin (m + 1)) (k : Nat) : Finset (Fin (m + 1)) :=
  Nat.rec {s} (fun _ r => r ∪ Finset.univ.filter
    (fun v => ∃ u ∈ r, IntegerGrid.manhattan (point u) (point v) = 1)) k

theorem mem_succ (point : Fin (m + 1) → Int × Int) (s v : Fin (m + 1)) (k : Nat) :
    v ∈ reached point s (k + 1) ↔ v ∈ reached point s k ∨
      ∃ u ∈ reached point s k, (IntegerGrid.graph point).Adj u v := by
  change v ∈ reached point s k ∪ Finset.univ.filter _ ↔ _
  simp [IntegerGrid.graph, reached]

theorem reached_mono (point : Fin (m + 1) → Int × Int) (s : Fin (m + 1)) :
    Monotone (reached point s) := by
  apply monotone_nat_of_le_succ
  intro k v hv
  exact (mem_succ point s v k).mpr (Or.inl hv)

theorem reached_reachable (point : Fin (m + 1) → Int × Int) (s v : Fin (m + 1)) (k : Nat)
    (h : v ∈ reached point s k) : (IntegerGrid.graph point).Reachable s v := by
  induction k generalizing v with
  | zero =>
    have he : v = s := by simpa [reached] using h
    subst v
    exact ⟨.nil⟩
  | succ k ih =>
    rcases (mem_succ point s v k).mp h with h | ⟨u, hu, he⟩
    · exact ih v h
    · obtain ⟨p⟩ := ih u hu
      exact ⟨p.concat he⟩

theorem walk_reached (point : Fin (m + 1) → Int × Int) {s v : Fin (m + 1)}
    (p : (IntegerGrid.graph point).Walk s v) : v ∈ reached point s p.length := by
  induction p using SimpleGraph.Walk.concatRec with
  | Hnil => simp [reached]
  | @Hconcat u v w p he ih =>
    rw [SimpleGraph.Walk.length_concat, mem_succ]
    exact Or.inr ⟨v, ih, he⟩

theorem connected_iff (point : Fin (m + 1) → Int × Int) :
    (IntegerGrid.graph point).Connected ↔ reached point 0 m = Finset.univ := by
  constructor
  · intro hc
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨p, hp⟩ := hc.exists_isPath 0 v
    have hl := hp.length_lt
    simp only [Fintype.card_fin] at hl
    exact reached_mono point 0 (by omega) (walk_reached point p)
  · intro he
    apply (SimpleGraph.connected_iff_exists_forall_reachable (G := IntegerGrid.graph point)).mpr
    exact ⟨0, fun v => reached_reachable point 0 v m (by simp [he])⟩

def connectedTest (point : Fin (m + 1) → Int × Int) : Bool :=
  decide (reached point ⟨0, Nat.zero_lt_succ m⟩ m = Finset.univ)

theorem connectedTest_correct (point : Fin (m + 1) → Int × Int) :
    connectedTest point = true ↔ (IntegerGrid.graph point).Connected := by
  unfold connectedTest
  rw [decide_eq_true_eq]
  exact (connected_iff point).symm

end CliffordSynthesis.GridConnectivity
