/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineDegreeBundle
public import GridHardness.CorrectedSatScheduleGraph
public import GridHardness.PlanarSatTotalDegree

/-!
# Corrected SAT Degree

Directed degree preservation through the actual SAT insertion
schedule. The invariant uses finite cardinalities, independent of how the
changing vertex types are enumerated.
-/

@[expose] public section

namespace GridHardness.CorrectedSatDegree
open XorLineSchedule XorLineRegistry
open XorWire.NetworkDegree (inDegree outDegree)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

def Bounds (g : FiniteGraph) : Prop := ∀ v : g.Vertex,
  Nat.card {u : g.Vertex // g.adj u v} ≤ 2 ∧
  Nat.card {u : g.Vertex // g.adj v u} ≤ 2 ∧
  Nat.card {u : g.Vertex // g.adj u v} + Nat.card {u : g.Vertex // g.adj v u} ≤ 3

private theorem card_in {V : Type*} [Fintype V] (D : V → V → Prop) (v : V) :
    Nat.card {u : V // D u v} = inDegree D v := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private theorem card_out {V : Type*} [Fintype V] (D : V → V → Prop) (v : V) :
    Nat.card {u : V // D v u} = outDegree D v := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem bounds_iff (g : FiniteGraph) [Fintype g.Vertex] : Bounds g ↔
    ∀ v, inDegree g.adj v ≤ 2 ∧ outDegree g.adj v ≤ 2 ∧
      inDegree g.adj v + outDegree g.adj v ≤ 3 := by
  simp only [Bounds, card_in, card_out]

theorem cross_bounds {X B : Type} [DecidableEq X] [DecidableEq B]
    (s : State X B) (a : X) (b : B) (hd : Bounds s.toFiniteGraph) :
    Bounds (s.cross a b).toFiniteGraph := by
  classical
  let _ : Fintype s.Vertex := Fintype.ofFinite _
  let _ : Fintype (s.cross a b).Vertex := inferInstanceAs
    (Fintype ((s.registry.bundles b).RefinedVertex (s.registry.xors.embed a)))
  apply (bounds_iff _).mpr
  have h := (bounds_iff s.toFiniteGraph).mp hd
  intro v
  exact (s.registry.bundles b).refined_degree_bounds (s.registry.xors.embed a)
    (s.registry.xors.embed_injective a) (s.registry.xors.isolated a)
    (s.registry.xor_ne_source a b) (s.registry.xor_ne_target a b)
    (fun v => (h v).1) (fun v => (h v).2.1) (fun v => (h v).2.2) v

theorem crossMany_bounds {X B : Type} [DecidableEq X] [DecidableEq B]
    (s : State X B) (a : X) (bs : List B) (hd : Bounds s.toFiniteGraph) :
    Bounds (s.crossMany a bs).toFiniteGraph := by
  induction bs generalizing s with
  | nil => exact hd
  | cons b bs ih => exact ih (s.cross a b) (cross_bounds s a b hd)

theorem run_bounds {n : Nat} {B : Type} (p : Program n B) :
    ∀ [DecidableEq B] (s : State (Fin n) B), Bounds s.toFiniteGraph → Bounds (p.run s) := by
  induction p with
  | done => intro _ s hd; exact hd
  | insert bs rest ih =>
    intro _ s hd
    exact ih ((s.crossMany 0 bs).retire) (crossMany_bounds s 0 bs hd)

private theorem indegree_filter {V : Type*} [Fintype V] (D : V → V → Prop)
    [DecidableRel D] (v : V) :
    inDegree D v = (Finset.univ.filter (fun u => D u v)).card := by
  unfold inDegree
  congr 1
  ext u
  simp only [Finset.mem_filter]

private theorem outdegree_filter {V : Type*} [Fintype V] (D : V → V → Prop)
    [DecidableRel D] (v : V) :
    outDegree D v = (Finset.univ.filter (fun u => D v u)).card := by
  unfold outDegree
  congr 1
  ext u
  simp only [Finset.mem_filter]

theorem initial_bounds {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    Bounds (CorrectedSatSchedule.initialState φ).toFiniteGraph := by
  let _ : Fintype (CorrectedSatSchedule.initialState φ).Vertex :=
    inferInstanceAs (Fintype (PlanarSatAssembly.Vertex n m))
  apply (bounds_iff _).mpr
  intro v
  change PlanarSatAssembly.Vertex n m at v
  change inDegree (PlanarSatAssembly.Adj φ) v ≤ 2 ∧
    outDegree (PlanarSatAssembly.Adj φ) v ≤ 2 ∧
    inDegree (PlanarSatAssembly.Adj φ) v + outDegree (PlanarSatAssembly.Adj φ) v ≤ 3
  rw [indegree_filter, outdegree_filter]
  exact ⟨PlanarSatAssembly.indegree_le_two φ v, PlanarSatAssembly.outdegree_le_two φ v,
    PlanarSatAssembly.total_degree_le_three φ v⟩

theorem graph_bounds {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (cells : List (Nat × Nat)) : Bounds (CorrectedSatSchedule.graph φ cells) :=
  run_bounds (CorrectedSatSchedule.plan (3*m) cells) _ (initial_bounds φ)

theorem actual_bounds (x : CliffordComplexity.SatTy.denote) :
    Bounds (CorrectedSatSchedule.actualGraph x) := graph_bounds _ _

theorem invalid_bounds : Bounds CorrectedSatSchedule.invalidGraph := by
  intro v
  change Nat.card {u : Fin 2 // False} ≤ 2 ∧ Nat.card {u : Fin 2 // False} ≤ 2 ∧
    Nat.card {u : Fin 2 // False} + Nat.card {u : Fin 2 // False} ≤ 3
  simp

theorem positive_bounds (x : CliffordComplexity.SatTy.denote) :
    Bounds (CorrectedSatSchedule.positiveGraph x) := by
  unfold CorrectedSatSchedule.positiveGraph
  split
  · exact actual_bounds x
  · exact invalid_bounds

end
end GridHardness.CorrectedSatDegree
