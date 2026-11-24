/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalPermutationCoreEdges

/-!
# Corrected SAT Interval True Edges

Direction-sensitive true-port invariants. External variable-chain
edges survive both their active rows and all later crossings of their
retired wires. Mandatory internal XOR arcs are deliberately excluded.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.TrueEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def truePort (incoming : Bool) : Fin 8 := if incoming then 3 else 0

/-- A protected endpoint is either outside a live XOR or its appropriate
true port. Once retired, it avoids the end of any bundle arc that a future
subdivision would detach in the relevant direction. -/
structure Safe {n : Nat} (s : IntervalState n) (incoming : Bool) (v : s.Vertex) : Prop where
  xor : ∀ a k, s.positioned.registry.xors.embed a k=v → k=truePort incoming
  bundle : ∀ b i, endpoint (s.positioned.registry.bundles b) (i,incoming)≠v

variable {n : Nat}

private theorem endpointTag_old (which : Fin 4 → Bool) (side : Bool)
    (i : Fin 4) (incoming : Bool) (t : Slot)
    (h : BundleSegments.endpointTag which (side, (i, incoming)) =.inl t) :
    t=(i,incoming) := by
  cases incoming <;> simp only [BundleSegments.endpointTag] at h <;>
    split at h <;> simp_all

theorem cross_safe (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (incoming : Bool) (v : s.Vertex)
    (hv : Safe s incoming v) :
    Safe (s.cross a line height hc) incoming (crossLift s a line height hc v) := by
  constructor
  · intro b k he
    by_cases hba : b=a
    · subst b
      rw [← crossLift_current_xor] at he
      exact hv.xor a k (CoreEdges.crossLift_injective s a line height hc he)
    · rw [← crossLift_other_xor s a b hba line height hc] at he
      exact hv.xor b k (CoreEdges.crossLift_injective s a line height hc he)
  · intro b i
    by_cases ha : v∈Set.range (s.positioned.registry.xors.embed a)
    · obtain ⟨k,rfl⟩ := ha
      rw [crossLift_current_xor]
      exact ((s.cross a line height hc).positioned.registry.disjoint a b k (i,incoming)).symm
    · let o : Boundary.Outside s a := ⟨v,ha⟩
      have h := crossLift_survivor s a line height hc o
      change crossLift s a line height hc v = _ at h
      rw [h]
      change endpoint (s.positioned.registry.splitBundle a (s.select line height hc).val
        BundleSegments.towardTrue b) (i,incoming)≠_
      cases b with
      | inl b =>
        change endpoint (s.positioned.registry.crossBundle a (s.select line height hc).val b.val)
          (i,incoming)≠_
        rw [Registry.crossBundle_other _ _ _ _ b.property]
        intro he
        exact hv.bundle b.val i (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj he)))
      | inr side =>
        change endpoint (BundleSegments.side (s.positioned.registry.bundles (s.select line height hc).val)
          (s.positioned.registry.xors.embed a) _ _
          (BundleSegments.selected BundleSegments.towardTrue side)) (i,incoming)≠_
        rw [BundleSegments.side_endpoint_tag]
        cases he : BundleSegments.endpointTag BundleSegments.towardTrue (side,(i,incoming)) with
        | inl t =>
          obtain rfl := endpointTag_old BundleSegments.towardTrue side i incoming t he
          intro h
          exact hv.bundle (s.select line height hc).val i
            (Sum.inl.inj (congrArg Subtype.val (Sum.inl.inj h)))
        | inr t => intro h; cases h

theorem retire_safe (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (incoming : Bool)
    (v : s.Vertex) (hv : Safe s incoming v) :
    Safe (s.retire line upper hfresh) incoming v := by
  constructor
  · intro a k he
    exact hv.xor a.succ k he
  · intro b i
    cases b with
    | none =>
      change endpoint (s.positioned.registry.xors.bundle 0) (i,incoming)≠v
      rw [family_endpoint]
      intro he
      have hp := hv.xor 0 (xorEndpoint (i,incoming)) he
      have hn : ∀ (i : Fin 4) (b : Bool), xorEndpoint (i,b)≠truePort b := by decide +kernel
      exact hn i incoming hp
    | some b => exact hv.bundle b i

/-- Exact preservation at one crossing. The two protected endpoints may
belong to different live XORs, to already retired wires, or to bodies. -/
theorem cross_adj (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (u v : s.Vertex) (hu : Safe s false u)
    (hv : Safe s true v) :
    (s.cross a line height hc).adj (crossLift s a line height hc u)
      (crossLift s a line height hc v) ↔ s.adj u v := by
  by_cases hua : u∈Set.range (s.positioned.registry.xors.embed a)
  · obtain ⟨k,hk⟩ := hua
    have hk0 : k=0 := hu.xor a k hk
    subst k
    subst u
    rw [crossLift_current_xor]
    by_cases hva : v∈Set.range (s.positioned.registry.xors.embed a)
    · obtain ⟨k,hk⟩ := hva
      have hk3 : k=3 := hv.xor a k hk
      subst k
      subst v
      rw [crossLift_current_xor]
      exact ((s.cross a line height hc).positioned.registry.xors.isolated a).internal 0 3 |>.trans
        ((s.positioned.registry.xors.isolated a).internal 0 3).symm
    · let o : Boundary.Outside s a := ⟨v,hva⟩
      have h := crossLift_survivor s a line height hc o
      change crossLift s a line height hc v = _ at h
      rw [h]
      exact Boundary.true_outgoing s a line height hc o
  · let ou : Boundary.Outside s a := ⟨u,hua⟩
    have hlu := crossLift_survivor s a line height hc ou
    change crossLift s a line height hc u = _ at hlu
    rw [hlu]
    by_cases hva : v∈Set.range (s.positioned.registry.xors.embed a)
    · obtain ⟨k,hk⟩ := hva
      have hk3 : k=3 := hv.xor a k hk
      subst k
      subst v
      rw [crossLift_current_xor]
      exact Boundary.true_incoming s a line height hc ou
    · let ov : Boundary.Outside s a := ⟨v,hva⟩
      have hlv := crossLift_survivor s a line height hc ov
      change crossLift s a line height hc v = _ at hlv
      rw [hlv]
      change (s.adj u v ∧ ¬∃ k, u=(s.positioned.registry.bundles (s.select line height hc).val).source k ∧
        v=(s.positioned.registry.bundles (s.select line height hc).val).target k) ↔ _
      constructor
      · exact And.left
      · intro h
        refine ⟨h,?_⟩
        rintro ⟨k,hk,_⟩
        exact hu.bundle (s.select line height hc).val k hk.symm

theorem row_safe (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (incoming : Bool) (v : s.Vertex) (hv : Safe s incoming v) :
    Safe (s.crossRequests a height rs hn hc) incoming (rowLift s a height rs hn hc v) := by
  induction rs generalizing s with
  | nil => exact hv
  | cons i is ih =>
    exact ih (s.cross a i height (hc i (by simp))) (List.nodup_cons.mp hn).2
      (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) v) (cross_safe s a i height _ incoming v hv)

theorem row_adj (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (u v : s.Vertex) (hu : Safe s false u) (hv : Safe s true v) :
    (s.crossRequests a height rs hn hc).adj (rowLift s a height rs hn hc u)
      (rowLift s a height rs hn hc v) ↔ s.adj u v := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) (List.nodup_cons.mp hn).2
      (s.cross_remaining_covered a height i is hn hc)
      (crossLift s a i height (hc i (by simp)) u) (crossLift s a i height (hc i (by simp)) v)
      (cross_safe s a i height _ false u hu) (cross_safe s a i height _ true v hv)).trans
      (cross_adj s a i height _ u v hu hv)

theorem next_safe (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (incoming : Bool) (v : s.Vertex) (hv : Safe s incoming v) :
    Safe (next s height j h) incoming (nextLift s height j h v) :=
  retire_safe (crossed s height j h) j (height j) _ incoming _
    (row_safe s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered incoming v hv)

theorem next_adj (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (u v : s.Vertex) (hu : Safe s false u) (hv : Safe s true v) :
    (next s height j h).adj (nextLift s height j h u) (nextLift s height j h v) ↔ s.adj u v :=
  row_adj s 0 (height j) (requests height j) (requests_nodup height j) h.requests_covered u v hu hv

theorem run_safe (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 <height i) (n : Nat) : ∀ (j : Nat) (s : IntervalState n)
    (h : Ready s height j) (incoming : Bool) (v : s.Vertex), Safe s incoming v →
    Safe (runState height hinj hpos n j s h) incoming (runLift height hinj hpos n j s h v) := by
  induction n with
  | zero => intro j s h incoming v hv; exact hv
  | succ n ih =>
    intro j s h incoming v hv
    exact ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) incoming
      (nextLift s height j h v) (next_safe s height j h incoming v hv)

/-- The whole sweep preserves every protected outgoing-to-incoming
adjacency and nonadjacency, for arbitrary positive injective heights. -/
theorem run_adj (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 <height i) (n : Nat) : ∀ (j : Nat) (s : IntervalState n)
    (h : Ready s height j) (u v : s.Vertex), Safe s false u → Safe s true v →
    ((runState height hinj hpos n j s h).adj (runLift height hinj hpos n j s h u)
      (runLift height hinj hpos n j s h v) ↔ s.adj u v) := by
  induction n with
  | zero => intro j s h u v hu hv; rfl
  | succ n ih =>
    intro j s h u v hu hv
    exact (ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
      (nextLift s height j h u) (nextLift s height j h v)
      (next_safe s height j h false u hu) (next_safe s height j h true v hv)).trans
      (next_adj s height j h u v hu hv)

open PlanarSatAssembly
variable {m : Nat}

theorem core_safe (s : IntervalState n) (incoming : Bool) (v : s.Vertex)
    (hv : CoreEdges.Core s v) : Safe s incoming v where
  xor := fun a k he => False.elim (hv.xor a k he)
  bundle := fun b i => hv.bundle b (i,incoming)

def OriginalSafe (incoming : Bool) (v : PlanarSatAssembly.Vertex n m) : Prop :=
  ∀ o k, PlanarSatAssembly.xor o k=v → k=truePort incoming

theorem body_original_safe (incoming : Bool) (v : PlanarSatAssembly.Vertex n m)
    (hv : CoreEdges.Body v) : OriginalSafe incoming v :=
  fun o k he => False.elim (hv o k he)

theorem xor_original_safe (incoming : Bool) (o : Occurrence m) :
    OriginalSafe incoming (PlanarSatAssembly.xor (n := n) o (truePort incoming)) := by
  intro a k he
  simpa only [PlanarSatAssembly.xor,Sum.inr.injEq,Prod.mk.injEq] using
    (congrArg Prod.snd (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj he))))

theorem initial_safe (φ : Formula n m) (incoming : Bool)
    (v : PlanarSatAssembly.Vertex n m) (hv : OriginalSafe incoming v) :
    Safe (initialState φ) incoming v where
  xor := fun a k he => hv ((SatWireLayout.variableRank φ).symm a) k he
  bundle := fun b => b.elim

theorem initial_safe_iff (φ : Formula n m) (incoming : Bool)
    (v : PlanarSatAssembly.Vertex n m) :
    Safe (initialState φ) incoming v ↔ OriginalSafe incoming v := by
  constructor
  · intro hv o k he
    apply hv.xor ((SatWireLayout.variableRank φ) o) k
    change PlanarSatAssembly.xor
      ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) k=v
    simpa only [Equiv.symm_apply_apply] using he
  · exact initial_safe φ incoming v

/-- An arbitrary occurrence permutation preserves precisely the old
adjacency between protected original endpoints, retaining their original
names. This includes endpoints whose XOR has already retired. -/
theorem permutation_adj (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (u v : PlanarSatAssembly.Vertex n m)
    (hu : OriginalSafe false u) (hv : OriginalSafe true v) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p u)
      (PermutationGraph.liftOriginal φ p v) ↔ Adj φ u v :=
  run_adj (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
    (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p) u v
    (initial_safe φ false u hu) (initial_safe φ true v hv)

def ChainSource (v : PlanarSatAssembly.Vertex n m) : Prop :=
  (∃ w, v=var w false) ∨ ∃ o, v=PlanarSatAssembly.xor o 0

def ChainTarget (v : PlanarSatAssembly.Vertex n m) : Prop :=
  (∃ w, v=var w true) ∨ ∃ o, v=PlanarSatAssembly.xor o 3

theorem chain_source_safe (v : PlanarSatAssembly.Vertex n m) (hv : ChainSource v) :
    OriginalSafe false v := by
  rcases hv with ⟨w,rfl⟩ | ⟨o,rfl⟩
  · exact body_original_safe false _ (CoreEdges.var_body w false)
  · exact xor_original_safe false o

theorem chain_target_safe (v : PlanarSatAssembly.Vertex n m) (hv : ChainTarget v) :
    OriginalSafe true v := by
  rcases hv with ⟨w,rfl⟩ | ⟨o,rfl⟩
  · exact body_original_safe true _ (CoreEdges.var_body w true)
  · exact xor_original_safe true o

theorem variable_chain_endpoints (φ : Formula n m) (w : Fin n)
    (u v : PlanarSatAssembly.Vertex n m) (h : (u, v) ∈variableChain φ w) :
    ChainSource u ∧ ChainTarget v := by
  have hs := (List.of_mem_zip h).1
  have ht := (List.of_mem_zip h).2
  constructor
  · simp only [List.mem_cons,List.mem_map] at hs
    rcases hs with rfl | ⟨o,_,rfl⟩
    · exact Or.inl ⟨w,rfl⟩
    · exact Or.inr ⟨o,rfl⟩
  · simp only [List.mem_append,List.mem_map,List.mem_singleton] at ht
    rcases ht with ⟨o,_,rfl⟩ | rfl
    · exact Or.inr ⟨o,rfl⟩
    · exact Or.inl ⟨w,rfl⟩

theorem variable_chain_edge (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (w : Fin n) (u v : PlanarSatAssembly.Vertex n m) (h : (u, v) ∈variableChain φ w) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p u)
      (PermutationGraph.liftOriginal φ p v) := by
  have hb := variable_chain_endpoints φ w u v h
  apply (permutation_adj φ p u v (chain_source_safe u hb.1) (chain_target_safe v hb.2)).2
  simp only [PlanarSatAssembly.Adj,edges,List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr
    ⟨w,List.mem_finRange w,List.mem_cons_of_mem _ h⟩)))

theorem chain_adj_iff_source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (u v : PlanarSatAssembly.Vertex n m) (hu : ChainSource u) (hv : ChainTarget v) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p u)
      (PermutationGraph.liftOriginal φ p v) ↔ Adj φ u v :=
  permutation_adj φ p u v (chain_source_safe u hu) (chain_target_safe v hv)

/-- Among the variable-side endpoints, the source assembly has exactly
the direct variable branches and the listed occurrence-chain links. -/
theorem source_chain_adj (φ : Formula n m)
    (u v : PlanarSatAssembly.Vertex n m) (hu : ChainSource u) (hv : ChainTarget v) :
    Adj φ u v ↔
      (∃ w, u=var w false ∧ v=var w true) ∨ ∃ w, (u,v)∈variableChain φ w := by
  constructor
  · intro h
    simp only [PlanarSatAssembly.Adj,edges,List.mem_append] at h
    rcases h with (((hs | hb) | hw) | hc) | hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with hs | hs
      all_goals
        have he := congrArg Prod.fst hs
        rcases hu with ⟨w,hu⟩ | ⟨o,hu⟩ <;>
          simp [hu,sent,var,PlanarSatAssembly.xor] at he
    · have hm := (List.of_mem_zip hb).1
      rcases hu with ⟨w,rfl⟩ | ⟨o,rfl⟩ <;>
        simp [slots,sent,var,clause,PlanarSatAssembly.xor] at hm
    · obtain ⟨w,_,hw⟩ := List.mem_flatMap.mp hw
      rcases List.mem_cons.mp hw with he | he
      · exact Or.inl ⟨w,congrArg Prod.fst he,congrArg Prod.snd he⟩
      · exact Or.inr ⟨w,he⟩
    · obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨⟨a,b⟩,_,he⟩ := List.mem_map.mp hc
      have he := congrArg Prod.fst he
      rcases hu with ⟨w,hu⟩ | ⟨o,hu⟩ <;>
        simp [hu,clause,var,PlanarSatAssembly.xor] at he
    · obtain ⟨o,_,ho⟩ := List.mem_flatMap.mp hx
      rcases List.mem_append.mp ho with ho | ho
      · rcases hu with ⟨w,rfl⟩ | ⟨a,rfl⟩ <;>
          simp [clauseLinks,clause,var,PlanarSatAssembly.xor] at ho
      · obtain ⟨e,_,he⟩ := List.mem_map.mp ho
        rcases hu with ⟨w,rfl⟩ | ⟨a,rfl⟩
        · have hs := congrArg Prod.fst he
          simp [var,PlanarSatAssembly.xor] at hs
        · rcases hv with ⟨w,rfl⟩ | ⟨b,rfl⟩
          · have ht := congrArg Prod.snd he
            simp [var,PlanarSatAssembly.xor] at ht
          · have hs := congrArg Prod.fst he
            have ht := congrArg Prod.snd he
            simp only [PlanarSatAssembly.xor,Sum.inr.injEq,Prod.mk.injEq] at hs ht
            have hn : ∀ e : Fin 10, XorGadget.arc e≠(0,3) := by decide +kernel
            exact False.elim (hn e (Prod.ext hs.2 ht.2))
  · intro h
    simp only [PlanarSatAssembly.Adj,edges,List.mem_append]
    apply Or.inl
    apply Or.inl
    apply Or.inr
    rcases h with ⟨w,rfl,rfl⟩ | ⟨w,hw⟩
    · exact List.mem_flatMap.mpr ⟨w,List.mem_finRange w,by simp⟩
    · exact List.mem_flatMap.mpr ⟨w,List.mem_finRange w,List.mem_cons_of_mem _ hw⟩

/-- Complete final adjacency between original variable-side endpoints,
without assuming that the candidate pair was already an edge. -/
theorem chain_adj_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (u v : PlanarSatAssembly.Vertex n m) (hu : ChainSource u) (hv : ChainTarget v) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p u)
      (PermutationGraph.liftOriginal φ p v) ↔
      (∃ w, u=var w false ∧ v=var w true) ∨ ∃ w, (u,v)∈variableChain φ w :=
  (chain_adj_iff_source φ p u v hu hv).trans (source_chain_adj φ u v hu hv)

end GridHardness.CorrectedSatInterval.TrueEdges
