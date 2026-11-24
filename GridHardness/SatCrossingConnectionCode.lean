/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalCatalogue
public import GridHardness.XorLineCodeGeneric

/-!
# SAT Crossing Connection Code

A list-bounded compiler for the horizontal connections between consecutive
crossing cells. The emitted pairs satisfy the actual geometric routing
condition, and both execution cost and encoded output size are polynomial.
This is a component of the drawing compiler, not a complete SAT reduction.
-/

@[expose] public section

namespace GridHardness.SatCrossingConnectionCode
open CliffordComplexity SatCrossingCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev ConnectionTy := Ty.pair PairTy PairTy
abbrev ConnectionsTy := Ty.list ConnectionTy

/-- Two cells share a row and are ordered from left to right. -/
def forward : Code ConnectionTy .bool := Code.and
  (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq)
  (Code.lt (.comp .fst .fst) (.comp .snd .fst))

theorem forward_eval (a b : Nat × Nat) :
    forward.eval (a,b) = true ↔ a.2=b.2 ∧ a.1<b.1 := by
  change (decide (a.2=b.2) && Code.natLt.eval (a.1,b.1)) = true ↔ _
  rw [Bool.and_eq_true, decide_eq_true_eq, natLt_eval_true]

/-- A third cell obstructs the proposed consecutive connection. -/
def between : Code (.pair ConnectionTy PairTy) .bool := Code.and
  (.comp (.pair (.comp (.comp .fst .fst) .snd) (.comp .snd .snd)) .natEq)
  (Code.and (Code.lt (.comp (.comp .fst .fst) .fst) (.comp .snd .fst))
    (Code.lt (.comp .snd .fst) (.comp (.comp .fst .snd) .fst)))

theorem between_eval (a b c : Nat × Nat) :
    between.eval ((a,b),c) = true ↔ a.2=c.2 ∧ a.1<c.1 ∧ c.1<b.1 := by
  change (decide (a.2=c.2) && (Code.natLt.eval (a.1,c.1) &&
    Code.natLt.eval (c.1,b.1))) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, natLt_eval_true, natLt_eval_true]

def consecutiveTest : Code (.pair PairListTy ConnectionTy) .bool := Code.and
  (.comp .snd forward)
  (Code.isNil (.comp (.pair .snd .fst) (Code.filterEnv between)))

theorem consecutiveTest_eval (l : List (Nat × Nat)) (a b : Nat × Nat) :
    consecutiveTest.eval (l,(a,b)) = true ↔
      a.2=b.2 ∧ a.1<b.1 ∧ ∀ c∈l, a.2=c.2 → a.1<c.1 → b.1≤c.1 := by
  change (forward.eval (a,b) &&
    (Code.isNil (.comp (.pair .snd .fst) (Code.filterEnv between))).eval (l,(a,b))) = true ↔ _
  rw [Bool.and_eq_true, forward_eval, isNil_eval_true]
  change (a.2=b.2 ∧ a.1<b.1) ∧ (Code.filterEnv between).eval ((a,b),l)=[] ↔ _
  rw [filterEnv_eval, List.filter_eq_nil_iff]
  constructor
  · rintro ⟨⟨he,hab⟩,h⟩
    refine ⟨he,hab,?_⟩
    intro c hc he hac
    have hn := h c hc
    have ht := between_eval a b c
    by_contra hnle
    have ht' := ht.mpr ⟨he,hac,by omega⟩
    simp [ht'] at hn
  · rintro ⟨he,hab,h⟩
    refine ⟨⟨he,hab⟩,?_⟩
    intro c hc
    cases ht : between.eval ((a,b),c)
    · simp
    · obtain ⟨he,hac,hcb⟩ := (between_eval a b c).mp ht
      have hbc := h c hc he hac
      omega

def connections : Code PairListTy ConnectionsTy :=
  .comp (.pair .id (.comp (.pair .id .id) Code.cross)) (Code.filterEnv consecutiveTest)

theorem connections_eval (l : List (Nat × Nat)) :
    connections.eval l = (l.product l).filter (fun e => consecutiveTest.eval (l,e)) := by
  change (Code.filterEnv consecutiveTest).eval (l,Code.cross.eval (l,l)) = _
  rw [filterEnv_eval]
  rfl

theorem mem_connections (l : List (Nat × Nat)) (a b : Nat × Nat) :
    (a,b) ∈ connections.eval l ↔ a∈l ∧ b∈l ∧ a.2=b.2 ∧ a.1<b.1 ∧
      ∀ c∈l, a.2=c.2 → a.1<c.1 → b.1≤c.1 := by
  rw [connections_eval, List.mem_filter, consecutiveTest_eval]
  have hp : (a,b) ∈ l.product l ↔ a∈l ∧ b∈l := List.mem_product
  rw [hp]
  tauto

theorem connections_nodup (l : List (Nat × Nat)) (hl : l.Nodup) :
    (connections.eval l).Nodup := by
  rw [connections_eval]
  exact (hl.product hl).filter _

theorem connections_length_le (l : List (Nat × Nat)) :
    (connections.eval l).length ≤ l.length*l.length := by
  rw [connections_eval, ← List.length_product]
  exact List.length_filter_le _ _

theorem successor_unique (l : List (Nat × Nat)) (a b c : Nat × Nat)
    (hb : (a, b) ∈connections.eval l) (hc : (a, c) ∈connections.eval l) : b=c := by
  obtain ⟨_,hbl,hab,hltb,hbnext⟩ := (mem_connections l a b).mp hb
  obtain ⟨_,hcl,hac,hltc,hcnext⟩ := (mem_connections l a c).mp hc
  exact Prod.ext (le_antisymm (hbnext c hcl hac hltc) (hcnext b hbl hab hltb))
    (hab.symm.trans hac)

/-- At most one connection leaves each crossing. The quadratic candidate
search therefore emits at most as many connections as there are cells. -/
theorem connections_length_le_cells (l : List (Nat × Nat)) (hl : l.Nodup) :
    (connections.eval l).length ≤ l.length := by
  have hn : ((connections.eval l).map Prod.fst).Nodup := by
    apply List.Nodup.map_on _ (connections_nodup l hl)
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd he
    dsimp at he
    subst c
    exact Prod.ext rfl (successor_unique l a b d hab hcd)
  have hs : (connections.eval l).map Prod.fst ⊆ l := by
    intro a ha
    obtain ⟨⟨b,c⟩,hbc,he⟩ := List.mem_map.mp ha
    subst a
    exact ((mem_connections l b c).mp hbc).1
  simpa only [List.length_map] using hn.length_le_of_subset hs

/-- Emit cell pairs directly from the finite SAT occurrence catalogue. -/
def horizontal : Code SatTy ConnectionsTy := .comp crossings connections

theorem horizontal_correct (x : SatTy.denote) (i k j : Fin (3 *x.length)) :
    ((i.val,j.val),(k.val,j.val)) ∈ horizontal.eval x ↔
      SatCrossingHorizontal.ConsecutiveColumns
        (SatWireLayout.permutation (finiteFormula x)) i k j := by
  change _ ∈ connections.eval (crossings.eval x) ↔ _
  rw [mem_connections, crossing_cell_iff, crossing_cell_iff]
  constructor
  · rintro ⟨hi,hk,_,hik,h⟩
    refine ⟨hi,hk,hik,?_⟩
    intro a ha hia
    exact h (a.val,j.val) ((crossing_cell_iff x a j).mpr ha) rfl hia
  · rintro ⟨hi,hk,hik,h⟩
    refine ⟨hi,hk,rfl,hik,?_⟩
    rintro ⟨a,b⟩ hc he hia
    dsimp at he hia ⊢
    subst b
    obtain ⟨ha,_⟩ := crossing_bounds x (a,j.val) hc
    exact h ⟨a,ha⟩ ((crossing_cell_iff x ⟨a,ha⟩ j).mp hc) hia

theorem horizontal_nodup (x : SatTy.denote) : (horizontal.eval x).Nodup :=
  connections_nodup _ (crossings_nodup x)

theorem horizontal_length_le (x : SatTy.denote) :
    (horizontal.eval x).length ≤ 9*x.length*x.length :=
  (connections_length_le_cells _ (crossings_nodup x)).trans (crossings_length_le x)

end GridHardness.SatCrossingConnectionCode
