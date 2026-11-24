/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatDegree

/-!
# Planar SAT Total Degree

The concrete SAT assembly has total directed degree at most three.
The proof counts its internal neighbours and its actual external ports;
no Hamiltonian traversal or satisfiability hypothesis is used.
-/

@[expose] public section

namespace GridHardness.PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Vertices which can source a link joining two construction blocks. -/
def externalOutPort {n m : Nat} : Vertex n m → Bool
  | .inl i => decide (i = 2)
  | .inr (.inl _) => true
  | .inr (.inr (.inl (_, i))) => decide (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 8)
  | .inr (.inr (.inr (_, i))) => decide (i = 0 ∨ i = 7)

/-- Vertices which can receive a link joining two construction blocks. -/
def externalInPort {n m : Nat} : Vertex n m → Bool
  | .inl i => decide (i = 0)
  | .inr (.inl _) => true
  | .inr (.inr (.inl (_, i))) => decide (i = 1 ∨ i = 5 ∨ i = 8 ∨ i = 9)
  | .inr (.inr (.inr (_, i))) => decide (i = 3 ∨ i = 4)

theorem external_source_port {n m : Nat} (φ : Formula n m) {a b : Vertex n m}
    (he : External φ a b) : externalOutPort a = true := by
  rcases he with hb | ⟨v, hv⟩ | ⟨o, ho⟩
  · have hm := (List.of_mem_zip hb).1
    simp only [slots, List.map_append, List.map_cons, List.map_nil, List.map_map,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hm
    rcases hm with (rfl | ⟨v, _, rfl⟩) | ⟨c, _, rfl⟩ <;> rfl
  · have hm := (List.of_mem_zip hv).1
    simp only [List.mem_cons, List.mem_map] at hm
    rcases hm with rfl | ⟨o, _, rfl⟩ <;> rfl
  · simp only [clauseLinks, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ho
    rcases ho with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · rcases o with ⟨c, j⟩
      fin_cases j <;> rfl
    · rfl

theorem external_target_port {n m : Nat} (φ : Formula n m) {a b : Vertex n m}
    (he : External φ a b) : externalInPort b = true := by
  rcases he with hb | ⟨v, hv⟩ | ⟨o, ho⟩
  · have hm := (List.of_mem_zip hb).2
    rcases List.mem_append.mp hm with hm | hm
    · have ht := List.mem_of_mem_tail hm
      simp only [slots, List.map_append, List.map_cons, List.map_nil, List.map_map,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at ht
      rcases ht with (rfl | ⟨v, _, rfl⟩) | ⟨c, _, rfl⟩ <;> rfl
    · have h := List.mem_singleton.mp hm
      subst b
      rfl
  · have hm := (List.of_mem_zip hv).2
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
    rcases hm with ⟨o, _, rfl⟩ | rfl <;> rfl
  · simp only [clauseLinks, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ho
    rcases ho with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rfl
    · rcases o with ⟨c, j⟩
      fin_cases j <;> rfl

private theorem neighbor_count_le {V : Type*} [Fintype V] (R E : V → Prop)
    [DecidablePred R] (inside : List V) (port : Bool)
    (hr : ∀ v, R v → v ∈ inside ∨ E v)
    (he : ∀ u v, E u → E v → u = v)
    (hp : ∀ v, E v → port = true) :
    (Finset.univ.filter R).card ≤ inside.length + if port then 1 else 0 := by
  classical
  by_cases h : ∃ v, E v
  · obtain ⟨v, hv⟩ := h
    have hsub : Finset.univ.filter R ⊆ inside.toFinset ∪ {v} := by
      intro w hw
      rcases hr w (Finset.mem_filter.mp hw).2 with hw | hw
      · exact Finset.mem_union_left _ (List.mem_toFinset.mpr hw)
      · exact Finset.mem_union_right _ (by simpa using he w v hw hv)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hi := List.toFinset_card_le inside
    rw [hp v hv]
    simp only [Finset.card_singleton, ite_true] at *
    omega
  · have hsub : Finset.univ.filter R ⊆ inside.toFinset := by
      intro w hw
      rcases hr w (Finset.mem_filter.mp hw).2 with hw | hw
      · exact List.mem_toFinset.mpr hw
      · exact False.elim (h ⟨w, hw⟩)
    have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le inside)
    split_ifs <;> omega

theorem outdegree_port_bound {n m : Nat} (φ : Formula n m) (a : Vertex n m) :
    (Finset.univ.filter (fun b => Adj φ a b)).card ≤
      (internalSuccessors a).length + if externalOutPort a then 1 else 0 :=
  neighbor_count_le (Adj φ a) (External φ a) (internalSuccessors a) (externalOutPort a)
    (fun _ h => outgoing_internal_or_external φ h)
    (fun _ _ h h' => external_target_unique φ h h')
    (fun _ h => external_source_port φ h)

theorem indegree_port_bound {n m : Nat} (φ : Formula n m) (a : Vertex n m) :
    (Finset.univ.filter (fun b => Adj φ b a)).card ≤
      (internalPredecessors a).length + if externalInPort a then 1 else 0 :=
  neighbor_count_le (fun b => Adj φ b a) (fun b => External φ b a)
    (internalPredecessors a) (externalInPort a)
    (fun _ h => incoming_internal_or_external φ h)
    (fun _ _ h h' => external_source_unique φ h h')
    (fun _ h => external_target_port φ h)

theorem local_total_capacity {n m : Nat} (a : Vertex n m) :
    ((internalSuccessors a).length + if externalOutPort a then 1 else 0) +
      ((internalPredecessors a).length + if externalInPort a then 1 else 0) ≤ 3 := by
  rcases a with i | (⟨v, b⟩ | (⟨c, i⟩ | ⟨o, i⟩))
  · fin_cases i <;> simp [internalSuccessors, internalPredecessors, externalOutPort, externalInPort]
  · cases b <;> simp [internalSuccessors, internalPredecessors, externalOutPort, externalInPort]
  · fin_cases i <;> simp [internalSuccessors, internalPredecessors, externalOutPort,
      externalInPort, clauseInternal, clausePredecessors]
  · fin_cases i <;> simp [internalSuccessors, internalPredecessors, externalOutPort,
      externalInPort, xorInternal, xorPredecessors]

/-- For every formula and every vertex, the number of incoming plus outgoing
arcs is at most three, including the actual inter-gadget links. -/
theorem total_degree_le_three {n m : Nat} (φ : Formula n m) (a : Vertex n m) :
    (Finset.univ.filter (fun b => Adj φ b a)).card +
      (Finset.univ.filter (fun b => Adj φ a b)).card ≤ 3 := by
  have hi := indegree_port_bound φ a
  have ho := outdegree_port_bound φ a
  have ht := local_total_capacity a
  omega

/-- At least one directed side has at most one incident arc, the condition
needed to orient the singleton-port local replacement. -/
theorem singleton_side {n m : Nat} (φ : Formula n m) (a : Vertex n m) :
    (Finset.univ.filter (fun b => Adj φ b a)).card ≤ 1 ∨
      (Finset.univ.filter (fun b => Adj φ a b)).card ≤ 1 := by
  have h := total_degree_le_three φ a
  omega

end GridHardness.PlanarSatAssembly
