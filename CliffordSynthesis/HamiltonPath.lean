/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PathRows
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.InformationTheory.Hamming

/-!
# Hamilton Path

Extracting a Hamiltonian path in the induced cube graph, using Mathlib's
actual graph walks and Hamiltonian-path predicate.
-/

@[expose] public section

namespace CliffordSynthesis.HamiltonPath

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open RowHistory (rowAt newRow)
open StandardSpace (standard)
open RecorderVectors (parity)
open PathRows (pathWire Certified)
open Target (Wire)

variable {d r n m : Nat}

def cubeGraph (vertex : Fin (m + 1) → Fin d → F) : SimpleGraph (Fin (m + 1)) where
  Adj u v := hammingDist (vertex u) (vertex v) = 1
  symm := ⟨by intro u v h; rwa [hammingDist_comm]⟩
  loopless := ⟨by intro u; simp⟩

theorem parity_step_distance (label : Wire d r ≃ Fin n) (u v : Fin d → F) (j : Fin d)
    (h : parity label v = parity label u + (standard n).x (label (.inl j))) : hammingDist u v = 1 := by
  classical
  have hk : ∀ k, v k = u k + if k = j then 1 else 0 := by
    intro k
    simpa only [RecorderVectors.parity_coordinate, Pi.add_apply, RecorderVectors.basis_apply, Sum.inl.injEq] using
      congrFun h (label (.inl k), false)
  have hs : Finset.univ.filter (fun k => u k ≠ v k) = {j} := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp [hk]
    · simp [hk, hkj]
  rw [hammingDist, hs, Finset.card_singleton]

/-- Each circuit prefix gives a simple cube walk. Its support is precisely the
vertex parities seen on the path wire up to that prefix. -/
theorem prefix_walk (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (hv : Function.Injective vertex) (hzero : vertex 0 = 0) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) :
    ∃ v, ∃ p : (cubeGraph vertex).Walk 0 v,
      p.IsPath ∧ runRows pre (standard n).x (pathWire label) = parity label (vertex v) ∧
      ∀ u, u ∈ p.support ↔ ∃ s ≤ pre.length, rowAt cs (standard n).x s (pathWire label) = parity label (vertex u) := by
  induction pre using List.reverseRecOn generalizing post with
  | nil =>
    refine ⟨0, .nil, by simp, ?_, ?_⟩
    · simp only [RowHistory.run_nil, hzero, RecorderVectors.zero_parity, pathWire]
    · intro u
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton, List.length_nil, Nat.le_zero]
      constructor
      · intro hu
        subst u
        exact ⟨0, rfl, by simp [rowAt, RowHistory.run_nil, hzero, RecorderVectors.zero_parity, pathWire]⟩
      · rintro ⟨s, rfl, hu⟩
        apply hv
        apply RecorderVectors.parity_injective label
        simpa only [rowAt, List.take_zero, RowHistory.run_nil, hzero, RecorderVectors.zero_parity, pathWire] using hu.symm
  | append_singleton pre g ih =>
    have heq' : cs = pre ++ g :: post := by simpa only [List.append_assoc, List.singleton_append] using heq
    obtain ⟨v, p, hp, hvp, hsupport⟩ := ih (g :: post) heq'
    by_cases ht : g.target = pathWire label
    · obtain ⟨w, hw⟩ := PathRows.path_birth label vertex X cs h pre post g heq' ht
      obtain ⟨j, hj⟩ := PathRows.path_step label vertex X cs h pre post g heq' ht
      have hedge : (cubeGraph vertex).Adj v w.succ := by
        exact parity_step_distance label _ _ j (hw.symm.trans (hj.trans (by rw [hvp])))
      have hafter : runRows (pre ++ [g]) (standard n).x (pathWire label) = parity label (vertex w.succ) := by
        rw [RowHistory.run_append, RowHistory.run_singleton]
        simpa only [newRow, ht] using hw
      have hat : rowAt cs (standard n).x (pre.length + 1) (pathWire label) = parity label (vertex w.succ) := by
        rw [heq', RowHistory.at_after]
        simpa only [newRow, ht] using hw
      have hnot : w.succ ∉ p.support := by
        intro hm
        obtain ⟨s, hs, hv⟩ := (hsupport w.succ).mp hm
        exact h.fresh pre g post heq' s hs (pathWire label) (hw.trans hv.symm)
      refine ⟨w.succ, p.concat hedge, ?_, hafter, ?_⟩
      · apply SimpleGraph.Walk.IsPath.mk'
        simp only [SimpleGraph.Walk.support_concat, List.nodup_append, hp.support_nodup,
          List.nodup_singleton, true_and, List.mem_singleton]
        intro a ha b hb
        subst b
        intro he
        exact hnot (he ▸ ha)
      · intro u
        simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton,
          List.length_append, List.length_singleton]
        constructor
        · rintro (hu | hu)
          · obtain ⟨s, hs, he⟩ := (hsupport u).mp hu
            exact ⟨s, by omega, he⟩
          · subst u
            exact ⟨pre.length + 1, le_rfl, hat⟩
        · rintro ⟨s, hs, he⟩
          by_cases hs' : s ≤ pre.length
          · exact Or.inl ((hsupport u).mpr ⟨s, hs', he⟩)
          · have hse : s = pre.length + 1 := by omega
            exact Or.inr (hv (RecorderVectors.parity_injective label (he.symm.trans (hse ▸ hat))))
    · have hafter : runRows (pre ++ [g]) (standard n).x (pathWire label) = parity label (vertex v) := by
        rw [RowHistory.run_append, RowHistory.run_singleton]
        simpa only [addRow, ite_eq_right (Ne.symm ht)] using hvp
      have hat : rowAt cs (standard n).x (pre.length + 1) (pathWire label) = parity label (vertex v) := by
        rw [heq', RowHistory.at_after]
        simpa only [addRow, ite_eq_right (Ne.symm ht)] using hvp
      refine ⟨v, p, hp, hafter, ?_⟩
      intro u
      simp only [List.length_append, List.length_singleton]
      constructor
      · intro hu
        obtain ⟨s, hs, he⟩ := (hsupport u).mp hu
        exact ⟨s, by omega, he⟩
      · rintro ⟨s, hs, he⟩
        by_cases hs' : s ≤ pre.length
        · exact (hsupport u).mpr ⟨s, hs', he⟩
        · have hse : s = pre.length + 1 := by omega
          have huv : u = v := hv (RecorderVectors.parity_injective label (he.symm.trans (hse ▸ hat)))
          subst u
          exact p.end_mem_support

/-- Replication forces every vertex parity onto the path wire itself. -/
theorem all_vertices_on_path (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = RecorderVectors.embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m)
    (v : Fin (m + 1)) :
    ∃ s ≤ cs.length, rowAt cs (standard n).x s (pathWire label) = parity label (vertex v) := by
  have hc := PathRows.certified_target label vertex hv hzero copies cs t hout hbudget
  obtain ⟨s, hs, i, hi⟩ := ReplicatedTarget.all_parities_visible label vertex copies
    (RowHistory.asCircuit cs) t (ClassicalTarget.circuit_final label cs t _ hout)
    (by simpa only [RowHistory.circuit_cost] using hbudget) v
  have hs' : s ≤ cs.length := by simpa only [RowHistory.asCircuit, List.length_map] using hs
  have hr : runRows (cs.take s) (standard n).x i = parity label (vertex v) := by
    exact Option.some.inj (by simpa only [RowHistory.visible_at, rowAt] using hi)
  have hcs : cs = cs.take s ++ cs.drop s := (List.take_append_drop s cs).symm
  have hip := PathRows.parity_location label vertex _ cs hc (cs.take s) (cs.drop s) hcs i (vertex v) hr
  exact ⟨s, hs', by simpa only [rowAt, hip] using hr⟩

/-- Soundness of the concrete reduction at the mathematical level: a bounded
classical implementation of the target produces a specified-endpoint
Hamiltonian path in the induced cube graph. -/
theorem classical_implies_hamiltonian (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (last : Fin (m + 1))
    (hout : ∀ i, runRows cs (standard n).x i = RecorderVectors.embed label (Target.matrix (vertex last)
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    ∃ p : (cubeGraph vertex).Walk 0 last, p.IsHamiltonian := by
  have hc := PathRows.certified_target label vertex hv hzero copies cs (vertex last) hout hbudget
  obtain ⟨v, p, hp, hend, hsupport⟩ := prefix_walk label vertex hv hzero _ cs hc cs [] (by simp)
  have hlast : runRows cs (standard n).x (pathWire label) = parity label (vertex last) := by
    simpa only [pathWire, Equiv.symm_apply_apply, RecorderVectors.target_path_row] using hout (pathWire label)
  have hvl : v = last := hv (RecorderVectors.parity_injective label (hend.symm.trans hlast))
  subst v
  refine ⟨p, hp.isHamiltonian_of_mem ?_⟩
  intro u
  exact (hsupport u).mpr (all_vertices_on_path label vertex hv hzero copies cs (vertex last) hout hbudget u)

/-- The actual Boolean bounded Clifford-synthesis predicate implies the source
Hamiltonian-path predicate. No recorder, freshness, path, or external-hardness
hypothesis is assumed. -/
theorem synthesis_implies_hamiltonian (vertex : Fin (m + 1) → Fin d → F)
    (hv : Function.Injective vertex) (hzero : vertex 0 = 0) (last : Fin (m + 1))
    (h : Circuit.SynthesizesWithin (EncodedTarget.instanceTableau vertex last) (EncodedTarget.recorderCount m + m)) :
    ∃ p : (cubeGraph vertex).Walk 0 last, p.IsHamiltonian := by
  obtain ⟨cs, hlen, hout⟩ := EncodedTarget.synthesis_to_row_circuit vertex hv hzero last h
  exact classical_implies_hamiltonian (EncodedTarget.physicalLabel d (EncodedTarget.recorderCount m))
    vertex hv hzero (EncodedTarget.copies m) cs last hout (Nat.le_of_eq hlen)

end CliffordSynthesis.HamiltonPath
