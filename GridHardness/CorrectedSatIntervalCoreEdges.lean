/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalGlobalNumbering

/-!
# Corrected SAT Interval Core Edges

Vertices outside all live XORs and all registered bundle endpoints are
unaffected by crossing refinements. Their invariant and exact mutual
adjacency are preserved through any entire two-sided interval sweep.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.CoreEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A body vertex is outside every piece of wiring that a later step may
replace or subdivide. This is checked on actual vertex identities. -/
structure Core {n : Nat} (s : IntervalState n) (v : s.Vertex) : Prop where
  xor : ∀ a k, s.positioned.registry.xors.embed a k≠v
  bundle : ∀ b q, endpoint (s.positioned.registry.bundles b) q≠v

variable {n : Nat}

def outside (s : IntervalState n) (a : Fin n) (v : s.Vertex) (hv : Core s v) :
    Boundary.Outside s a := ⟨v,by rintro ⟨k,hk⟩; exact hv.xor a k hk⟩

theorem crossLift_injective (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) : Function.Injective (crossLift s a line height hc) := by
  intro u v h
  exact Sum.inl.inj ((Numbering.equiv s a line height hc).symm.injective h)

/-- Outside vertices remain outside every live XOR and every surviving or
new residual bundle after a crossing. -/
theorem cross_core (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : s.Vertex) (hv : Core s v) :
    Core (s.cross a line height hc) (crossLift s a line height hc v) := by
  constructor
  · intro b k he
    by_cases hba : b=a
    · subst b
      rw [← crossLift_current_xor] at he
      exact hv.xor a k (crossLift_injective s a line height hc he)
    · rw [← crossLift_other_xor s a b hba line height hc] at he
      exact hv.xor b k (crossLift_injective s a line height hc he)
  · intro b q
    have h := crossLift_survivor s a line height hc (outside s a v hv)
    change crossLift s a line height hc v = _ at h
    rw [h]
    change endpoint (s.positioned.registry.splitBundle a (s.select line height hc).val
      BundleSegments.towardTrue b) q≠_
    cases b with
    | inl b =>
      change endpoint (s.positioned.registry.crossBundle a (s.select line height hc).val b.val) q≠_
      rw [Registry.crossBundle_other _ _ _ _ b.property]
      intro he
      exact hv.bundle b.val q (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj he)))
    | inr side =>
      change endpoint (BundleSegments.side (s.positioned.registry.bundles (s.select line height hc).val)
        (s.positioned.registry.xors.embed a) _ _
        (BundleSegments.selected BundleSegments.towardTrue side)) q≠_
      rw [BundleSegments.side_endpoint_tag]
      cases he : BundleSegments.endpointTag BundleSegments.towardTrue (side,q) with
      | inl t =>
        intro h
        exact hv.bundle (s.select line height hc).val t
          (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj h)))
      | inr t => intro h; cases h

/-- For two core vertices, the crossing changes neither direction of
adjacency. The subdivided arcs cannot have either vertex as an endpoint. -/
theorem cross_adj (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (u v : s.Vertex) (hu : Core s u) (hv : Core s v) :
    (s.cross a line height hc).adj (crossLift s a line height hc u)
      (crossLift s a line height hc v) ↔ s.adj u v := by
  have hlu := crossLift_survivor s a line height hc (outside s a u hu)
  have hlv := crossLift_survivor s a line height hc (outside s a v hv)
  change crossLift s a line height hc u = _ at hlu
  change crossLift s a line height hc v = _ at hlv
  rw [hlu, hlv]
  change (s.adj u v ∧ ¬∃ k, u=(s.positioned.registry.bundles (s.select line height hc).val).source k ∧
    v=(s.positioned.registry.bundles (s.select line height hc).val).target k) ↔ _
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    rintro ⟨k,hk,_⟩
    exact hu.bundle (s.select line height hc).val (k,false) hk.symm

/-- Retirement changes no graph edges, and its newly registered endpoints
come from the retired XOR, which core vertices already avoid. -/
theorem retire_core (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (v : s.Vertex) (hv : Core s v) :
    Core (s.retire line upper hfresh) v := by
  constructor
  · intro a k
    exact hv.xor a.succ k
  · intro b q
    cases b with
    | none =>
      change endpoint (s.positioned.registry.xors.bundle 0) q≠v
      rw [family_endpoint]
      exact hv.xor 0 (xorEndpoint q)
    | some b => exact hv.bundle b q

/-- The core invariant is propagated by the actual recursive row lift. -/
theorem row_core (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (v : s.Vertex) (hv : Core s v) :
    Core (s.crossRequests a height rs hn hc) (rowLift s a height rs hn hc v) := by
  induction rs generalizing s with
  | nil => exact hv
  | cons i is ih =>
    exact ih (s.cross a i height (hc i (by simp))) (List.nodup_cons.mp hn).2
      (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) v) (cross_core s a i height _ v hv)

theorem row_adj (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (u v : s.Vertex) (hu : Core s u) (hv : Core s v) :
    (s.crossRequests a height rs hn hc).adj (rowLift s a height rs hn hc u)
      (rowLift s a height rs hn hc v) ↔ s.adj u v := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) (List.nodup_cons.mp hn).2
      (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) u) (crossLift s a i height (hc i (by simp)) v)
      (cross_core s a i height _ u hu) (cross_core s a i height _ v hv)).trans
      (cross_adj s a i height _ u v hu hv)

theorem next_core (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (v : s.Vertex) (hv : Core s v) :
    Core (next s height j h) (nextLift s height j h v) :=
  retire_core (crossed s height j h) j (height j) _ _
    (row_core s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered v hv)

theorem next_adj (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (u v : s.Vertex) (hu : Core s u) (hv : Core s v) :
    (next s height j h).adj (nextLift s height j h u) (nextLift s height j h v) ↔ s.adj u v :=
  row_adj s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered u v hu hv

/-- Any injective positive height schedule preserves all core vertices. -/
theorem run_core (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 <height i) (n : Nat) : ∀ (j : Nat) (s : IntervalState n)
    (h : Ready s height j) (v : s.Vertex), Core s v →
    Core (runState height hinj hpos n j s h) (runLift height hinj hpos n j s h v) := by
  induction n with
  | zero => intro j s h v hv; exact hv
  | succ n ih =>
    intro j s h v hv
    exact ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
      (nextLift s height j h v) (next_core s height j h v hv)

/-- Exact adjacency preservation through an entire sweep, for arbitrary
injective positive heights. No geometric drawing is assumed. -/
theorem run_adj (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 <height i) (n : Nat) : ∀ (j : Nat) (s : IntervalState n)
    (h : Ready s height j) (u v : s.Vertex), Core s u → Core s v →
    ((runState height hinj hpos n j s h).adj (runLift height hinj hpos n j s h u)
      (runLift height hinj hpos n j s h v) ↔ s.adj u v) := by
  induction n with
  | zero => intro j s h u v hu hv; rfl
  | succ n ih =>
    intro j s h u v hu hv
    exact (ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
      (nextLift s height j h u) (nextLift s height j h v)
      (next_core s height j h u hu) (next_core s height j h v hv)).trans
      (next_adj s height j h u v hu hv)

open PlanarSatAssembly
variable {m : Nat}

/-- Original vertices belonging to the sentinel, a variable body, or a
clause body, rather than an occurrence XOR. -/
def Body (v : PlanarSatAssembly.Vertex n m) : Prop :=
  ∀ o k, PlanarSatAssembly.xor o k≠v

theorem sent_body (i : Fin 3) : Body (sent (n := n) (m := m) i) := by
  intro o k h
  cases h

theorem var_body (v : Fin n) (b : Bool) : Body (var (m := m) v b) := by
  intro o k h
  cases h

theorem clause_body (c : Fin m) (v : Fin 12) : Body (clause (n := n) c v) := by
  intro o k h
  cases h

/-- All body vertices satisfy the full invariant initially: every live
XOR is an occurrence XOR and there are no registered bundles yet. -/
theorem initial_core (φ : Formula n m) (v : PlanarSatAssembly.Vertex n m)
    (hv : Body v) : Core (initialState φ) v := by
  constructor
  · intro a k
    exact hv ((SatWireLayout.variableRank φ).symm a) k
  · intro b
    exact b.elim

theorem initial_core_iff (φ : Formula n m) (v : PlanarSatAssembly.Vertex n m) :
    Core (initialState φ) v ↔ Body v := by
  constructor
  · intro hv o k
    have h := hv.xor ((SatWireLayout.variableRank φ) o) k
    change PlanarSatAssembly.xor
      ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) k≠v at h
    simpa only [Equiv.symm_apply_apply] using h
  · exact initial_core φ v

/-- The adjacency theorem applies directly to an initial SAT graph for any
permutation or other injective positive height schedule. -/
theorem body_run_adj (φ : Formula n m) (height : Nat → Nat)
    (hinj : Function.Injective height) (hpos : ∀ i, 0 <height i)
    (h : Ready (initialState φ) height 0)
    (u v : PlanarSatAssembly.Vertex n m) (hu : Body u) (hv : Body v) :
    (runState height hinj hpos (3*m) 0 (initialState φ) h).adj
      (runLift height hinj hpos (3*m) 0 (initialState φ) h u)
      (runLift height hinj hpos (3*m) 0 (initialState φ) h v) ↔ Adj φ u v :=
  run_adj height hinj hpos (3*m) 0 (initialState φ) h u v
    (initial_core φ u hu) (initial_core φ v hv)

/-- The completed concrete sweep has exactly the old adjacency between
original body vertices, including absence of edges. -/
theorem formula_adj (φ : Formula n m) (u v : PlanarSatAssembly.Vertex n m)
    (hu : Body u) (hv : Body v) :
    (graph φ).adj (formulaLift φ u) (formulaLift φ v) ↔ Adj φ u v :=
  body_run_adj φ (formulaHeight φ) (formulaHeight_injective φ) (formulaHeight_pos φ)
    (initial_ready φ) u v hu hv

theorem formula_sent_adj (φ : Formula n m) (u v : Fin 3) :
    (graph φ).adj (formulaLift φ (sent u)) (formulaLift φ (sent v)) ↔
      Adj φ (sent u) (sent v) :=
  formula_adj φ _ _ (sent_body u) (sent_body v)

theorem formula_variable_adj (φ : Formula n m) (u v : Fin n) (a b : Bool) :
    (graph φ).adj (formulaLift φ (var u a)) (formulaLift φ (var v b)) ↔
      Adj φ (var u a) (var v b) :=
  formula_adj φ _ _ (var_body u a) (var_body v b)

theorem formula_clause_adj (φ : Formula n m) (c d : Fin m) (u v : Fin 12) :
    (graph φ).adj (formulaLift φ (clause c u)) (formulaLift φ (clause d v)) ↔
      Adj φ (clause c u) (clause d v) :=
  formula_adj φ _ _ (clause_body c u) (clause_body d v)

/-- Each of the fourteen local clause-body arcs is an actual edge after
the entire sweep. -/
theorem formula_clause_edge (φ : Formula n m) (c : Fin m) (u v : Fin 12)
    (h : (u, v) ∈clauseBody) :
    (graph φ).adj (formulaLift φ (clause c u)) (formulaLift φ (clause c v)) := by
  apply (formula_clause_adj φ c c u v).2
  change (clause c u,clause c v)∈edges φ
  have hc : (clause (n := n) c u,clause c v)∈clauseEdges c :=
    List.mem_map.mpr ⟨(u,v),h,rfl⟩
  have hm : (clause (n := n) c u,clause c v)∈
      (List.finRange m).flatMap clauseEdges :=
    List.mem_flatMap.mpr ⟨c,List.mem_finRange c,hc⟩
  simp only [edges, List.mem_append]
  exact Or.inl (Or.inr hm)

/-- The direct variable branch survives even when the other branch runs
through many crossing cells. -/
theorem formula_variable_direct (φ : Formula n m) (v : Fin n) :
    (graph φ).adj (formulaLift φ (var v false)) (formulaLift φ (var v true)) := by
  apply (formula_variable_adj φ v v false true).2
  change (var v false,var v true)∈edges φ
  have hm : (var (m := m) v false,var v true)∈
      (List.finRange n).flatMap (fun w => (var w false,var w true)::variableChain φ w) :=
    List.mem_flatMap.mpr ⟨v,List.mem_finRange v,by simp⟩
  simp only [edges, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hm))

/-- Both endpoints of every original backbone edge are core vertices. -/
theorem backbone_body (u v : PlanarSatAssembly.Vertex n m)
    (h : (u, v) ∈backbone n m) : Body u ∧ Body v := by
  constructor
  · intro o k he
    subst u
    exact backbone_no_xor_source o k v h
  · intro o k he
    subst v
    exact backbone_no_xor_target o k u h

theorem formula_backbone_edge (φ : Formula n m) (u v : PlanarSatAssembly.Vertex n m)
    (h : (u, v) ∈backbone n m) :
    (graph φ).adj (formulaLift φ u) (formulaLift φ v) := by
  have hb := backbone_body u v h
  apply (formula_adj φ u v hb.1 hb.2).2
  change (u,v)∈edges φ
  simp only [edges, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

end GridHardness.CorrectedSatInterval.CoreEdges
