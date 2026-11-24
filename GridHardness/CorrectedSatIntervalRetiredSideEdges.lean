/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetainedEdges

/-!
# Corrected SAT Interval Retired Side Edges

The six nonmandatory arcs of each occurrence XOR survive the entire
crossing sweep under their original vertex names. The four transverse
mandatory arcs may be subdivided later, so they are excluded from the
exact induced-adjacency statement below.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.RetiredSideEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Avoid the end of a mandatory arc that subdivision detaches in the
specified direction. This is a property of the eight local XOR vertices. -/
def Direction (incoming : Bool) (v : Fin 8) : Prop :=
  ∀ i : Fin 4, xorEndpoint (i,incoming)≠v

instance (incoming : Bool) (v : Fin 8) : Decidable (Direction incoming v) :=
  inferInstanceAs (Decidable (∀ i : Fin 4, xorEndpoint (i,incoming)≠v))

abbrev Internal (u v : Fin 8) : Prop :=
  ∃ e : Fin 10, XorGadget.arc e=(u,v)

abbrev Side (u v : Fin 8) : Prop :=
  ∃ e : Fin 6, XorGadget.arc (SatCrossingRetirement.sideArc e)=(u,v)

def Nonmandatory (u v : Fin 8) : Prop :=
  ∀ i : Fin 4, XorGadget.arc (Marked.crossArc i)≠(u,v)

instance (u v : Fin 8) : Decidable (Nonmandatory u v) :=
  inferInstanceAs (Decidable (∀ i : Fin 4, XorGadget.arc (Marked.crossArc i)≠(u,v)))

theorem side_directions : ∀ e : Fin 6,
    Direction false (XorGadget.arc (SatCrossingRetirement.sideArc e)).1 ∧
    Direction true (XorGadget.arc (SatCrossingRetirement.sideArc e)).2 := by decide +kernel

theorem side_nonmandatory : ∀ e : Fin 6,
    Nonmandatory (XorGadget.arc (SatCrossingRetirement.sideArc e)).1
      (XorGadget.arc (SatCrossingRetirement.sideArc e)).2 := by decide +kernel

theorem internal_nonmandatory_iff_side : ∀ u v : Fin 8,
    Nonmandatory u v → (Internal u v ↔ Side u v) := by decide +kernel

variable {n : Nat}

theorem retire_apart (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (v : Fin 8) :
    RetainedEdges.Apart (s.retire line upper hfresh) (s.positioned.registry.xors.embed 0 v) :=
  fun a k he => s.positioned.registry.xors.distinct a.succ 0 (by simp) k v he

/-- The side-arc source and target become protected as soon as their XOR
retires, including when its row has no crossings. -/
theorem retire_safe (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (incoming : Bool)
    (v : Fin 8) (hv : Direction incoming v) :
    TrueEdges.Safe (s.retire line upper hfresh) incoming
      (s.positioned.registry.xors.embed 0 v) := by
  constructor
  · intro a k he
    exact False.elim (retire_apart s line upper hfresh v a k he)
  · intro b i
    cases b with
    | none =>
      change endpoint (s.positioned.registry.xors.bundle 0) (i,incoming)≠_
      rw [family_endpoint]
      intro he
      exact hv i ((s.positioned.registry.xors.embed_injective 0) he)
    | some b => exact (s.positioned.registry.disjoint 0 b v (i,incoming)).symm

/-- No sweep can introduce a new adjacency between the eight names of an
original XOR. Before retirement they name an isolated live XOR; afterward
they are outside all live XORs and subdivisions can only remove such arcs. -/
theorem run_internal_back (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (a : Fin n) (u v : Fin 8),
      (runState height hinj hpos n j s h).adj
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a u))
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a v)) →
      Internal u v := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a u v he
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _)) at he
      simp only [nextLift,rowLift_current_xor] at he
      exact ((crossed s height j h).positioned.registry.xors.isolated 0).internal u v |>.mp
        (RetainedEdges.run_adj_back height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h) _ _
          (retire_apart _ _ _ _ u) (retire_apart _ _ _ _ v) he)
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hb : b.succ=a := by apply Fin.ext; dsimp [b]; omega
      have hba : a≠0 := fun he => ha (congrArg Fin.val he)
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _)) at he
      simp only [nextLift,FalseEdges.rowLift_other_xor s 0 a hba] at he
      apply ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b u v
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)
            ((crossed s height j h).positioned.registry.xors.embed b.succ u))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)
            ((crossed s height j h).positioned.registry.xors.embed b.succ v))
      simpa only [hb,crossed] using he

/-- Exact adjacency in the protected directions through a complete sweep.
The protection is proved at retirement rather than assumed of the final
state. -/
theorem run_internal_iff (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (a : Fin n) (u v : Fin 8), Direction false u → Direction true v →
      ((runState height hinj hpos n j s h).adj
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a u))
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a v)) ↔
      Internal u v) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a u v hu hv
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      change ((runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _)) ↔ _)
      simp only [nextLift,rowLift_current_xor]
      exact (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (retire_safe _ _ _ _ false u hu) (retire_safe _ _ _ _ true v hv)).trans
        (((crossed s height j h).positioned.registry.xors.isolated 0).internal u v)
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hb : b.succ=a := by apply Fin.ext; dsimp [b]; omega
      have hba : a≠0 := fun he => ha (congrArg Fin.val he)
      change ((runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h) (nextLift s height j h _)) ↔ _)
      simp only [nextLift,FalseEdges.rowLift_other_xor s 0 a hba]
      have hi := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b u v hu hv
      change ((runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)
            ((crossed s height j h).positioned.registry.xors.embed b.succ u))
          (runLift height hinj hpos n (j+1) (next s height j h)
            (next_ready s height hinj hpos j h)
            ((crossed s height j h).positioned.registry.xors.embed b.succ v)) ↔ _) at hi
      simpa only [hb,crossed] using hi

open PlanarSatAssembly
variable {m : Nat}

/-- All candidate original-XOR adjacencies in the final graph come from
the ten original gadget arcs; there are no added internal arcs. -/
theorem permutation_internal_back (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (o : Occurrence m) (u v : Fin 8) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o u))
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o v)) → Internal u v := by
  have h := run_internal_back (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    ((SatWireLayout.variableRank φ) o) u v
  change (PermutationGraph.graph φ p).adj
    (PermutationGraph.liftOriginal φ p
      (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) u))
    (PermutationGraph.liftOriginal φ p
      (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) v)) →
    Internal u v at h
  simpa only [Equiv.symm_apply_apply] using h

theorem permutation_internal_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (o : Occurrence m) (u v : Fin 8) (hu : Direction false u) (hv : Direction true v) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o u))
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o v)) ↔ Internal u v := by
  have h := run_internal_iff (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    ((SatWireLayout.variableRank φ) o) u v hu hv
  change (PermutationGraph.graph φ p).adj
    (PermutationGraph.liftOriginal φ p
      (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) u))
    (PermutationGraph.liftOriginal φ p
      (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm ((SatWireLayout.variableRank φ) o)) v)) ↔
    Internal u v at h
  simpa only [Equiv.symm_apply_apply] using h

/-- Every one of the six side arcs is an actual final graph arc with its
original occurrence-XOR endpoint names. No geometric or safety premise is
needed. -/
theorem permutation_side_edge (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (o : Occurrence m) (e : Fin 6) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p
        (PlanarSatAssembly.xor o (XorGadget.arc (SatCrossingRetirement.sideArc e)).1))
      (PermutationGraph.liftOriginal φ p
        (PlanarSatAssembly.xor o (XorGadget.arc (SatCrossingRetirement.sideArc e)).2)) :=
  (permutation_internal_iff φ p o _ _ (side_directions e).1 (side_directions e).2).mpr
    ⟨SatCrossingRetirement.sideArc e,rfl⟩

/-- Excluding the four mandatory candidates, the induced graph on each
retired XOR consists exactly of its six side arcs. Mandatory candidates
are deliberately left open because they may survive unsplit. -/
theorem permutation_nonmandatory_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (o : Occurrence m) (u v : Fin 8) (h : Nonmandatory u v) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o u))
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor o v)) ↔ Side u v := by
  constructor
  · intro he
    exact (internal_nonmandatory_iff_side u v h).mp (permutation_internal_back φ p o u v he)
  · rintro ⟨e,he⟩
    have hs := permutation_side_edge φ p o e
    simpa only [he] using hs

/-- The same side-arc assertion under the simultaneous placement's wire
vertex naming, directly matching the retirement-side routes. -/
theorem placement_side_edge (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (j : Fin (3 *m)) (e : Fin 6) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.vertex φ p
        (.inl (j,(XorGadget.arc (SatCrossingRetirement.sideArc e)).1)))
      (PermutationWirePlacement.vertex φ p
        (.inl (j,(XorGadget.arc (SatCrossingRetirement.sideArc e)).2))) := by
  rw [PermutationWirePlacement.vertex_original,PermutationWirePlacement.vertex_original]
  exact permutation_side_edge φ p _ e

theorem placement_nonmandatory_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (j : Fin (3 *m)) (u v : Fin 8) (h : Nonmandatory u v) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.vertex φ p (.inl (j,u)))
      (PermutationWirePlacement.vertex φ p (.inl (j,v))) ↔ Side u v := by
  rw [PermutationWirePlacement.vertex_original,PermutationWirePlacement.vertex_original]
  exact permutation_nonmandatory_iff φ p _ u v h

end GridHardness.CorrectedSatInterval.RetiredSideEdges
