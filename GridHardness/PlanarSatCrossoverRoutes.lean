/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCrossoverRoutesFinite

/-!
# Planar SAT Crossover Routes

Classify the permitted single-orbit traversals of a crossover by their port choices.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover

def FollowsOption {V : Type*} (succ : V → V) (embed : Vertex → V)
    (u : Vertex) : Option Vertex → Prop
  | some v => succ (embed u) = embed v
  | none => ∀ v, succ (embed u) ≠ embed v

def FollowsCandidate {V : Type*} (succ : V → V) (embed : Vertex → V)
    (b : Rails) (top : Bool) : Prop := ∀ u, FollowsOption succ embed u (candidate b top u)

theorem forced_single {V : Type*} (succ : V → V) (embed : Vertex → V)
    (hg : Isolated succ embed) (u v : Vertex) (hne : u ∉ exits)
    (hn : neighbors u = [v]) : succ (embed u) = embed v := by
  obtain ⟨w, hw⟩ := hg.outgoing u hne
  have : w = v := by simpa [hn] using (adj_iff_neighbors u w).mp (hg.internal _ _ hw)
  simpa [this] using hw

theorem forced_binary {V : Type*} [DecidableEq V] (succ : V → V) (embed : Vertex → V)
    (hg : Isolated succ embed) (u v w : Vertex) (hne : u ∉ exits)
    (hn : neighbors u = [v, w]) :
    succ (embed u) = embed (if decide (succ (embed u) = embed v) then v else w) := by
  by_cases hs : succ (embed u) = embed v
  · simpa [hs] using hs
  · obtain ⟨z, hz⟩ := hg.outgoing u hne
    have hm := (adj_iff_neighbors u z).mp (hg.internal _ _ hz)
    simp only [hn, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact False.elim (hs hz)
    · simpa [hs] using hz

theorem optional_single {V : Type*} [DecidableEq V] (succ : V → V) (embed : Vertex → V)
    (hg : Isolated succ embed) (u v : Vertex) (hn : neighbors u = [v]) :
    FollowsOption succ embed u (if decide (succ (embed u) = embed v) then some v else none) := by
  by_cases hs : succ (embed u) = embed v
  · simpa [hs, FollowsOption] using hs
  · simp only [hs, decide_false, Bool.false_eq_true, ite_false, FollowsOption]
    intro w hw
    have : w = v := by simpa [hn] using (adj_iff_neighbors u w).mp (hg.internal _ _ hw)
    exact hs (by simpa [this] using hw)

theorem optional_after_forbidden {V : Type*} (succ : V → V) (embed : Vertex → V)
    (hg : Isolated succ embed) (u bad : Vertex) (out : Option Vertex)
    (hn : neighbors u = [bad] ++ out.toList) (hbad : succ (embed u) ≠ embed bad)
    (hne : out ≠ none → u ∉ exits) : FollowsOption succ embed u out := by
  cases out with
  | none =>
      intro v hv
      have : v = bad := by simpa [hn] using (adj_iff_neighbors u v).mp (hg.internal _ _ hv)
      exact hbad (by simpa [this] using hv)
  | some v =>
      obtain ⟨w, hw⟩ := hg.outgoing u (hne (by simp))
      have hm := (adj_iff_neighbors u w).mp (hg.internal _ _ hw)
      simp only [hn, Option.toList_some, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact False.elim (hbad hw)
      · exact hw

def railsOf {V : Type*} [DecidableEq V] (succ : V → V) (embed : Vertex → V) : Rails :=
  ![decide (succ (embed (h 0)) = embed (h 1)),
    decide (succ (embed (h 2)) = embed (h 1)),
    decide (succ (embed (h 5)) = embed (h 4)),
    decide (succ (embed (h 7)) = embed (h 6))]

/-- Once the five vertical XOR choices agree, every internal successor is
determined by just the four remaining horizontal rail choices. -/
theorem follows_candidate {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (embed : Vertex → V) (he : Function.Injective embed) (hg : Isolated succ embed)
    (top : Bool)
    (hv : ∀ i : Fin 5, PlanarSatXor.selection succ (embed ∘ x i) =
      if top then XorGadget.leftRoute else XorGadget.rightRoute) :
    FollowsCandidate succ embed (railsOf succ embed) top := by
  have hs (i : Fin 5) (e : Fin 10)
      (hbit : (if top then XorGadget.leftRoute else XorGadget.rightRoute) e = true) :=
    selection_step succ embed i _ (hv i) e hbit
  have cross (i : Fin 4) : succ (embed (h (crossSource i))) = embed (row i false) := by
    apply forced_single succ embed hg
    · fin_cases i <;> decide
    · fin_cases i <;> rfl
  have rowEnd (i : Fin 4) : succ (embed (row i true)) = embed (h (crossTarget i)) :=
    forced_single succ embed hg _ _ (by simp [row, exits, h, x]) rfl
  have rowStart (i : Fin 4) : succ (embed (row i false)) =
      embed (if top then x i.succ 3 else x i.castSucc 4) := by
    obtain ⟨v, hnext⟩ := hg.outgoing (row i false) (by simp [row, exits, h, x])
    have hn := (row_outgoing i v).mp (hg.internal _ _ hnext)
    cases ht : top
    · rcases hn with rfl | rfl
      · simpa [ht] using hnext
      · have hx := hs i.succ 3 (by simp [ht, XorGadget.rightRoute])
        have hc := he (succ.injective (hnext.trans hx.symm))
        simp [row, x, XorGadget.arc] at hc
    · rcases hn with rfl | rfl
      · have hx := hs i.castSucc 6 (by simp [ht, XorGadget.leftRoute])
        have hc := he (succ.injective (hnext.trans hx.symm))
        simp [row, x, XorGadget.arc] at hc
      · simpa [ht] using hnext
  have leftExit (ht : top = true) (i : Fin 5) :
      FollowsOption succ embed (x i 0) (leftOut i) := by
    apply optional_after_forbidden succ embed hg (x i 0) (x i 1) (leftOut i) rfl
    · intro hnext
      have hb := (PlanarSatXor.selection_true succ (embed ∘ x i) 0).mpr hnext
      rw [hv i] at hb
      simp [ht, XorGadget.leftRoute] at hb
    · intro hn
      fin_cases i <;> simp_all [leftOut, x, exits, h]
  have rightExit (ht : top = false) (i : Fin 5) :
      FollowsOption succ embed (x i 7) (rightOut i) := by
    apply optional_after_forbidden succ embed hg (x i 7) (x i 6) (rightOut i) rfl
    · intro hnext
      have hb := (PlanarSatXor.selection_true succ (embed ∘ x i) 9).mpr hnext
      rw [hv i] at hb
      simp [ht, XorGadget.rightRoute] at hb
    · intro hn
      fin_cases i <;> simp_all [rightOut, x, exits, h]
  intro u
  rcases u with j | ⟨i, out⟩ | ⟨i, j⟩
  · fin_cases j
    · exact optional_single succ embed hg (h 0) (h 1) rfl
    · exact cross 1
    · exact forced_binary succ embed hg (h 2) (h 1) (h 3) (by decide) rfl
    · exact cross 3
    · exact cross 0
    · exact forced_binary succ embed hg (h 5) (h 4) (h 6) (by decide) rfl
    · exact cross 2
    · exact optional_single succ embed hg (h 7) (h 6) rfl
  · cases out
    · exact rowStart i
    · exact rowEnd i
  · cases ht : top <;> fin_cases j
    · exact hs i 0 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 1 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 3 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 4 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 5 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 7 (by simp [ht, XorGadget.rightRoute])
    · exact hs i 8 (by simp [ht, XorGadget.rightRoute])
    · exact rightExit ht i
    · exact leftExit ht i
    · exact hs i 1 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 2 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 4 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 5 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 6 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 8 (by simp [ht, XorGadget.leftRoute])
    · exact hs i 9 (by simp [ht, XorGadget.leftRoute])

theorem FollowsCandidate.edge_iff {V : Type*} {succ : V → V} {embed : Vertex → V}
    {b : Rails} {top : Bool} (hf : FollowsCandidate succ embed b top)
    (he : Function.Injective embed) (u v : Vertex) :
    succ (embed u) = embed v ↔ candidate b top u = some v := by
  have hh := hf u
  cases hn : candidate b top u with
  | none =>
      rw [hn] at hh
      simp only [hn, reduceCtorEq, iff_false]
      exact hh v
  | some w =>
      rw [hn] at hh
      change succ (embed u) = embed w at hh
      constructor
      · intro hs
        have hw := he (hh.symm.trans hs)
        simp [hn, hw]
      · intro hs
        have hw : w = v := by simpa [hn] using hs
        simpa [hw] using hh

-- Kernel evaluation checks the possible local moves through the crossover.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the possible local moves through the crossover.
set_option synthInstance.maxSize 2048 in
theorem candidate_h1_targets : ∀ (b : Rails) (top : Bool) (u : Vertex),
    candidate b top u = some (h 1) ↔
      (u = h 0 ∧ b 0 = true) ∨ (u = h 2 ∧ b 1 = true) := by decide

-- Kernel evaluation checks the possible local moves through the crossover.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the possible local moves through the crossover.
set_option synthInstance.maxSize 2048 in
theorem candidate_h6_targets : ∀ (b : Rails) (top : Bool) (u : Vertex),
    candidate b top u = some (h 6) ↔
      (u = h 5 ∧ b 2 = false) ∨ (u = h 7 ∧ b 3 = true) := by decide

/-- The rail degree equations are consequences of the ambient permutation,
including the incoming-edge condition at the two non-port rail vertices. -/
theorem railDegree_of_follows {V : Type*} (succ : Equiv.Perm V) (embed : Vertex → V)
    (he : Function.Injective embed) (hg : Isolated succ embed)
    (b : Rails) (top : Bool) (hf : FollowsCandidate succ embed b top) : RailDegree b := by
  have h1yes : b 0 = true ∨ b 1 = true := by
    obtain ⟨u, hu⟩ := hg.incoming (h 1) (by decide)
    have hm := (candidate_h1_targets b top u).mp ((hf.edge_iff he u (h 1)).mp hu)
    exact hm.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have h1not : ¬(b 0 = true ∧ b 1 = true) := by
    rintro ⟨hb0, hb1⟩
    have h0 := (hf.edge_iff he (h 0) (h 1)).mpr (by simp [candidate, h, hb0])
    have h2 := (hf.edge_iff he (h 2) (h 1)).mpr (by simp [candidate, h, hb1])
    have hc := he (succ.injective (h0.trans h2.symm))
    simp [h] at hc
  have h6yes : b 2 = false ∨ b 3 = true := by
    obtain ⟨u, hu⟩ := hg.incoming (h 6) (by decide)
    have hm := (candidate_h6_targets b top u).mp ((hf.edge_iff he u (h 6)).mp hu)
    exact hm.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have h6not : ¬(b 2 = false ∧ b 3 = true) := by
    rintro ⟨hb2, hb3⟩
    have h5 := (hf.edge_iff he (h 5) (h 6)).mpr (by simp [candidate, h, hb2])
    have h7 := (hf.edge_iff he (h 7) (h 6)).mpr (by simp [candidate, h, hb3])
    have hc := he (succ.injective (h5.trans h7.symm))
    simp [h] at hc
  have hb : ∀ b : Rails, (b 0 = true ∨ b 1 = true) → ¬(b 0 = true ∧ b 1 = true) →
      (b 2 = false ∨ b 3 = true) → ¬(b 2 = false ∧ b 3 = true) → RailDegree b := by decide
  exact hb b h1yes h1not h6yes h6not

/-- An unintended candidate has a proper closed component of actual
successor edges. A single global spanning orbit excludes it. -/
theorem rails_classified {V : Type*} (succ : Equiv.Perm V) (ho : OneOrbit succ)
    (embed : Vertex → V) (he : Function.Injective embed) (hg : Isolated succ embed)
    (b : Rails) (top : Bool) (hf : FollowsCandidate succ embed b top) :
    b = leftRails ∨ b = rightRails := by
  rcases candidate_classification b top (railDegree_of_follows succ embed he hg b top hf) with
    hb | hb | ⟨hne, hout, hclosed⟩
  · exact Or.inl hb
  · exact Or.inr hb
  · obtain ⟨a, ha⟩ := hne
    have hc : ∀ w, (∃ u ∈ trapped b top, embed u = w) →
        ∃ u ∈ trapped b top, embed u = succ w := by
      rintro w ⟨u, hu, rfl⟩
      have hn := hclosed u hu
      cases hnxt : candidate b top u with
      | none => simp [hnxt] at hn
      | some v =>
          have hv : v ∈ trapped b top := by simpa [hnxt] using hn
          exact ⟨v, hv, ((hf.edge_iff he u v).mpr hnxt).symm⟩
    obtain ⟨u, hu, hue⟩ := ho.closed_spans
      (P := fun w => ∃ u ∈ trapped b top, embed u = w) ⟨a, ha, rfl⟩ hc
      (embed (verticalEntry top))
    exact False.elim (hout (he hue ▸ hu))

theorem exists_classified_candidate {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) : ∃ left top : Bool,
      FollowsCandidate succ embed (rails left) top := by
  obtain ⟨top, hv⟩ := vertical_uniform succ ho embed he hg
  have hf := follows_candidate succ embed he hg top hv
  rcases rails_classified succ ho embed he hg (railsOf succ embed) top hf with hl | hr
  · rw [hl] at hf
    exact ⟨true, top, hf⟩
  · rw [hr] at hf
    exact ⟨false, top, hf⟩

/-- Complete local traversal classification of the actual 56-vertex
crossover. Every internal successor edge belongs to exactly the prescribed
two paths. Their exits are precisely the vertices whose successors leave the
gadget, and their entries are precisely those with no internal predecessor.
Only ambient Hamiltonicity and the graph's incident-edge interface are assumed. -/
theorem route_classification {V : Type*} [DecidableEq V] (succ : Equiv.Perm V)
    (ho : OneOrbit succ) (embed : Vertex → V) (he : Function.Injective embed)
    (hg : Isolated succ embed) : ∃ left top : Bool,
    (horizontalPath left top).IsChain (fun u v => succ (embed u) = embed v) ∧
    (verticalPath top).IsChain (fun u v => succ (embed u) = embed v) ∧
    (∀ u v, succ (embed u) = embed v ↔ (u, v) ∈ pathLinks left top) ∧
    (∀ u, (∀ v, succ (embed u) ≠ embed v) ↔ u = horizontalExit left ∨ u = verticalExit top) ∧
    (∀ v, (∀ u, succ (embed u) ≠ embed v) ↔ v = horizontalEntry left ∨ v = verticalEntry top) := by
  obtain ⟨left, top, hf⟩ := exists_classified_candidate succ ho embed he hg
  obtain ⟨hh, hv, hlinks, hout, hin⟩ := classified_candidate left top
  refine ⟨left, top, hh.imp (fun u v hs => (hf.edge_iff he u v).mpr hs),
    hv.imp (fun u v hs => (hf.edge_iff he u v).mpr hs), ?_, ?_, ?_⟩
  · intro u v
    exact (hf.edge_iff he u v).trans (hlinks u v)
  · intro u
    calc
      (∀ v, succ (embed u) ≠ embed v) ↔ (∀ v, candidate (rails left) top u ≠ some v) :=
        forall_congr' (fun v => not_congr (hf.edge_iff he u v))
      _ ↔ candidate (rails left) top u = none := by
        cases candidate (rails left) top u <;> simp
      _ ↔ _ := hout u
  · intro v
    exact (forall_congr' (fun u => not_congr (hf.edge_iff he u v))).trans (hin v)

end GridHardness.PlanarSatCrossover
