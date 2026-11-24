/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Hamiltonian

Hamiltonian cycles expressed as spanning subgraphs, with enumeration and equivalence lemmas.
-/

public section

namespace GridHardness
open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

/-- A spanning cycle uses both incident edges at a vertex of degree two. -/
theorem adj_toSubgraph_iff_of_degree_eq_two [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {a v : V} {p : G.Walk a a} (hp : p.IsHamiltonianCycle) (hv : G.degree v = 2) (w : V) :
    p.toSubgraph.Adj v w ↔ G.Adj v w := by
  classical
  have hsmall := hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support v)
  have hlarge : (G.neighborSet v).ncard = 2 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree, hv]
  refine Subgraph.adj_iff_of_neighborSet_equiv (?_ : Nonempty _).some (Set.toFinite _)
  rw [← Cardinal.eq, ← Set.cast_ncard (Set.toFinite _),
    ← Set.cast_ncard (Walk.finite_neighborSet_toSubgraph p), hsmall, hlarge]

/-- A connected finite 2-regular graph is spanned by one cycle. -/
theorem exists_isHamiltonianCycle_of_isCycles [DecidableEq V] [Finite V] [Nontrivial V]
    (hdegree : G.IsCycles) (hconn : G.Connected) :
    ∃ a : V, ∃ p : G.Walk a a, p.IsHamiltonianCycle := by
  obtain ⟨a⟩ : Nonempty V := inferInstance
  have hsupport : a ∈ G.support := by rw [hconn.preconnected.support_eq_univ]; trivial
  obtain ⟨p, hcycle, hverts⟩ :=
    hdegree.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := G.connectedComponentMk a) rfl (G.mem_support.mp hsupport)
  refine ⟨a, p, isHamiltonianCycle_iff_isCycle_and_forall_mem_support.mpr ⟨hcycle, ?_⟩⟩
  intro v
  rw [← p.mem_verts_toSubgraph, hverts, ConnectedComponent.mem_supp_iff]
  exact ConnectedComponent.sound (hconn.preconnected v a)

theorem exists_isHamiltonianCycle_mono [DecidableEq V] {H : SimpleGraph V} (h : G ≤ H)
    (witness : ∃ a : V, ∃ p : G.Walk a a, p.IsHamiltonianCycle) :
    ∃ a : V, ∃ p : H.Walk a a, p.IsHamiltonianCycle := by
  obtain ⟨a, p, hp⟩ := witness
  exact ⟨a, p.map (.ofLE h), hp.map Function.bijective_id⟩

theorem exists_isHamiltonianCycle_iff_of_equiv {W : Type*} [DecidableEq V] [DecidableEq W]
    {H : SimpleGraph W} (e : V ≃ W) (adj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) :
    (∃ a : V, ∃ p : G.Walk a a, p.IsHamiltonianCycle) ↔
      ∃ b : W, ∃ q : H.Walk b b, q.IsHamiltonianCycle := by
  constructor
  · rintro ⟨a, p, hp⟩
    let f : G →g H := ⟨e, fun hab => (adj _ _).mp hab⟩
    exact ⟨e a, p.map f, hp.map (show Function.Bijective f from e.bijective)⟩
  · rintro ⟨b, q, hq⟩
    let f : H →g G := ⟨e.symm, fun hab => (adj _ _).mpr (by simpa using hab)⟩
    exact ⟨e.symm b, q.map f, hq.map (show Function.Bijective f from e.symm.bijective)⟩

/-- Enumerate the vertices of a spanning cycle in their order on the walk. -/
theorem enumerateCycle [Fintype V] [DecidableEq V] {a : V} {p : G.Walk a a}
    (hp : p.IsHamiltonianCycle) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∀ i, G.Adj (e i) (e (finRotate _ i)) := by
  have hlen := hp.length_eq
  let vert (i : Fin (Fintype.card V)) := p.getVert i.val
  have hinj : Function.Injective vert := by
    intro i j same
    apply Fin.ext
    exact hp.isCycle.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) same
  let e := Equiv.ofBijective vert
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩)
  refine ⟨e, fun i => ?_⟩
  change G.Adj (p.getVert i.val) (p.getVert (finRotate _ i).val)
  have step := p.adj_getVert_succ (i := i.val) (by omega)
  rw [val_finRotate]
  split_ifs with hi
  · rw [show i.val + 1 = p.length by omega, p.getVert_length] at step
    simpa using step
  · exact step

end GridHardness
