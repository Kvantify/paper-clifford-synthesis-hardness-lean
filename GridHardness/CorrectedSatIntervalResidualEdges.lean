/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalBundleTransport
public import GridHardness.SatCrossingResidualRoutes
public import GridHardness.CorrectedSatIntervalVerticalAnchors

/-!
# Corrected SAT Interval Residual Edges

A retired wire whose column contains no crossing keeps all four original
mandatory arcs. Their endpoint names are the original occurrence-XOR names,
exactly as used by the unsplit residual routes.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.ResidualEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The four transverse arcs survive when every later row is above the
retired column. This is a numerical sweep hypothesis, not graph safety. -/
theorem run_unsplit (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n),
      (∀ k, j+a.val<k → k<j+n → height (j+a.val)≤height k) →
      ∀ r : Fin 4,
      (runState height hinj hpos n j s h).adj
        (runLift height hinj hpos n j s h
          (s.positioned.registry.xors.embed a (XorGadget.arc (Marked.crossArc r)).1))
        (runLift height hinj hpos n j s h
          (s.positioned.registry.xors.embed a (XorGadget.arc (Marked.crossArc r)).2)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a ha r
    by_cases ha0 : a.val=0
    · have he : a=0 := Fin.ext ha0
      subst a
      have he := BundleTransport.run_edge height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) none (by
          intro k hk hkn hc
          have hh := ha k (by simpa using hk) (by omega)
          change j=j ∧ 0<height k ∧ height k<height j at hc
          simp only [Fin.val_zero,Nat.add_zero] at hh
          omega) r
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed 0
            (XorGadget.arc (Marked.crossArc r)).1))
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed 0
            (XorGadget.arc (Marked.crossArc r)).2)) at he
      simpa only [runState,runLift,nextLift,rowLift_current_xor,crossed] using he
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hb : b.succ=a := by apply Fin.ext; dsimp [b]; omega
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have he := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
        b (by intro k hk hkn; rw [hj] at hk ⊢; exact ha k hk (by omega)) r
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed b.succ
            (XorGadget.arc (Marked.crossArc r)).1))
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed b.succ
            (XorGadget.arc (Marked.crossArc r)).2)) at he
      simpa only [runState,runLift,nextLift,
        FalseEdges.rowLift_other_xor s 0 a (by intro hh; exact ha0 (congrArg Fin.val hh)),hb,crossed]
        using he

/-- The endpoint of a retired column, on the side containing a later
extremal crossing. -/
def residualLow (lower : Bool) (crossHeight : Nat) : Nat := if lower then 0 else crossHeight

def residualHigh (lower : Bool) (originalHeight crossHeight : Nat) : Nat :=
  if lower then crossHeight else originalHeight

theorem retirement_anchor {n : Nat} (s : IntervalState (n +1))
    (height : Nat → Nat) (j : Nat) (h : Ready s height j)
    (cutHeight : Nat) (hpos : 0 <cutHeight) (hcut : cutHeight <height j) (lower : Bool) :
    VerticalEdges.Anchored (next s height j h) j (residualLow lower cutHeight)
      (residualHigh lower (height j) cutHeight) lower
      (fun r => nextLift s height j h
        (s.positioned.registry.xors.embed 0 (xorEndpoint (VerticalEdges.boundarySlot lower r)))) := by
  refine ⟨none,rfl,?_,?_⟩
  · cases lower
    · exact ⟨rfl,hpos⟩
    · exact ⟨rfl,hcut⟩
  · intro r
    change endpoint ((crossed s height j h).positioned.registry.xors.bundle 0)
      (VerticalEdges.boundarySlot lower r)=_
    rw [family_endpoint]
    exact (rowLift_current_xor s 0 (height j) (requests height j)
      (requests_nodup height j) h.requests_covered _).symm

/-- A column extremum leaves every other later row outside the closed
residual interval. Permutation injectivity makes the inequalities strict. -/
theorem extremum_separated {N : Nat} (p : Equiv.Perm (Fin N)) (i j : Fin N)
    (lower : Bool)
    (he : if lower then SatCrossingRetirement.Segments.FirstInColumn p i j
      else SatCrossingRetirement.Segments.LastInColumn p i j)
    (k : Fin N) (hik : i <k) (hkj : k ≠j) :
    permutationHeight p k.val < residualLow lower (permutationHeight p j.val) ∨
      residualHigh lower (permutationHeight p i.val) (permutationHeight p j.val) <
        permutationHeight p k.val := by
  have hneq : p k≠p j := fun hh => hkj (p.injective hh)
  cases lower
  · simp only [Bool.false_eq_true,ite_false] at he
    simp only [residualLow,residualHigh,Bool.false_eq_true,ite_false,permutationHeight_apply]
    by_cases hact : SatCrossingRouting.Active p i k
    · left
      have hle := he.2 k hact
      have hlt : p k<p j := lt_of_le_of_ne hle hneq
      exact Nat.add_lt_add_right hlt 1
    · right
      have hle : p i≤p k := le_of_not_gt (fun hh => hact ⟨hik,hh⟩)
      have hne : p i≠p k := fun hh => (ne_of_lt hik) (p.injective hh)
      have hlt : p i<p k := lt_of_le_of_ne hle hne
      exact Nat.add_lt_add_right hlt 1
  · simp only [ite_true] at he
    simp only [residualLow,residualHigh,ite_true,permutationHeight_apply]
    right
    by_cases hact : SatCrossingRouting.Active p i k
    · have hle := he.2 k hact
      have hlt : p j<p k := lt_of_le_of_ne hle hneq.symm
      exact Nat.add_lt_add_right hlt 1
    · have hle : p i≤p k := le_of_not_gt (fun hh => hact ⟨hik,hh⟩)
      exact Nat.add_lt_add_right (he.1.2.trans_le hle) 1

open PlanarSatAssembly
variable {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

/-- An empty geometric column needs no assumed edge interface: all four
unsplit residual routes join actual final-graph arc endpoints. -/
theorem permutation_unsplit (i : Fin (3 *m))
    (hi : SatCrossingRetirement.Segments.EmptyColumn p i) (r : Fin 4) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.vertex φ p (.inl (i,(XorGadget.arc (Marked.crossArc r)).1)))
      (PermutationWirePlacement.vertex φ p (.inl (i,(XorGadget.arc (Marked.crossArc r)).2))) := by
  rw [PermutationWirePlacement.vertex_original,PermutationWirePlacement.vertex_original]
  apply run_unsplit (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p) i
  intro k hik hk
  let j : Fin (3*m) := ⟨k,by omega⟩
  have hh : ¬(p j).val<(p i).val := by
    intro hh
    exact hi j ⟨by change i.val<k; simpa using hik,hh⟩
  have hji : permutationHeight p k=(p j).val+1 := permutationHeight_apply p j
  simpa only [Nat.zero_add,permutationHeight_apply,hji] using Nat.add_le_add_right (Nat.le_of_not_gt hh) 1

end GridHardness.CorrectedSatInterval.ResidualEdges
