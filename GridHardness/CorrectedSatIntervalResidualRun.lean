/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalResidualEdges
public import GridHardness.CorrectedSatIntervalVerticalRun

/-!
# Corrected SAT Interval Residual Run

The upper and lower extremal crossings join the original retired-XOR
endpoints to actual retained crossing ports. The statements use the vertex
names of the complete sweep and hold for arbitrary occurrence permutations.
-/

public section

namespace GridHardness.CorrectedSatInterval.ResidualEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering HorizontalEdges VerticalEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Follow an original XOR to its retirement, then its boundary to the
specified extremal crossing. The resulting residual interval is an actual
bundle of the final registry, with both endpoint maps identified. -/
theorem run_residual_bundle (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a b : Fin n)
      (_hab : a<b) (lower : Bool)
      (_hheight : height (j+b.val)<height (j+a.val))
      (t : Fin (requests height (j+b.val)).length),
      (requests height (j+b.val))[t.val]=j+a.val →
      (∀ k, j+a.val<k → k<j+n → k≠j+b.val →
        height k<residualLow lower (height (j+b.val)) ∨
        residualHigh lower (height (j+a.val)) (height (j+b.val))<height k) →
      ∃ c : (runState height hinj hpos n j s h).BundleId,
        (runState height hinj hpos n j s h).positioned.segments c=
          ⟨j+a.val,residualLow lower (height (j+b.val)),
            residualHigh lower (height (j+a.val)) (height (j+b.val))⟩ ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c)
          (boundarySlot lower r)=runLift height hinj hpos n j s h
            (s.positioned.registry.xors.embed a (xorEndpoint (boundarySlot lower r)))) ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c)
          (boundarySlot (!lower) r)=runFresh height hinj hpos n j s h
            (rowIndex height n j b t) (boundaryPort (!lower) r)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a b hab lower hheight t ht hgap
    have hb0 : b.val≠0 := by have : a.val<b.val := hab; omega
    let b' : Fin n := ⟨b.val-1,by have := b.isLt; omega⟩
    have hjb : j+1+b'.val=j+b.val := by dsimp [b']; omega
    let t' : Fin (requests height (j+1+b'.val)).length :=
      ⟨t.val,by simpa only [hjb] using t.isLt⟩
    have hidx := rowIndex_succ height n j b hb0 t
    have hidx' : (rowIndex height (n+1) j b t).val=
        (rowIndex height n (j+1) b' t').val+(requests height j).length := hidx
    have hlt : ¬(rowIndex height (n+1) j b t).val<(requests height j).length := by omega
    have hindex : (⟨(rowIndex height (n+1) j b t).val-(requests height j).length,
        by have := (rowIndex height (n+1) j b t).isLt
           simp only [moveCount] at this
           omega⟩ : Fin (moveCount height n (j+1)))=rowIndex height n (j+1) b' t' := by
      apply Fin.ext
      dsimp only [Fin.val_mk]
      omega
    by_cases ha0 : a.val=0
    · have ha' : a=0 := Fin.ext ha0
      subst a
      have hheight' : height (j+b.val)<height j := by simpa using hheight
      have hord : residualLow lower (height (j+b.val))<
          residualHigh lower (height j) (height (j+b.val)) := by
        cases lower
        · exact hheight'
        · exact hpos _
      obtain ⟨c,hc,he,hf⟩ := anchored_run_connect height hinj hpos n (j+1)
        (next s height j h) (next_ready s height hinj hpos j h) j
        (residualLow lower (height (j+b.val)))
        (residualHigh lower (height j) (height (j+b.val))) hord lower
        (fun r => nextLift s height j h
          (s.positioned.registry.xors.embed 0 (xorEndpoint (boundarySlot lower r))))
        (retirement_anchor s height j h (height (j+b.val)) (hpos _) hheight' lower)
        b' t' (by simpa only [t',hjb,Fin.val_mk,Fin.val_zero,Nat.add_zero] using ht)
        (by rw [hjb]; cases lower <;> rfl)
        (by
          intro k hk hkn hne
          have hh := hgap k (by simpa using hk) (by omega) (by simpa only [hjb] using hne)
          simpa only [Fin.val_zero,Nat.add_zero] using hh)
      refine ⟨c,?_,he,?_⟩
      · simpa only [Fin.val_zero,Nat.add_zero,runState] using hc
      · intro r
        simpa only [runState,runFresh,dite_eq_right hlt,hindex] using hf r
    · let a' : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have ha : a'.succ=a := by apply Fin.ext; dsimp [a']; omega
      have hja : j+1+a'.val=j+a.val := by dsimp [a']; omega
      obtain ⟨c,hc,he,hf⟩ := ih (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) a' b' (by
          change a.val-1<b.val-1
          have : a.val<b.val := hab
          omega) lower
        (by simpa only [hja,hjb] using hheight) t'
        (by simpa only [hja,hjb,t',Fin.val_mk] using ht)
        (by
          intro k hk hkn hne
          rw [hja] at hk
          rw [hjb] at hne
          simpa only [hja,hjb] using hgap k hk (by omega) hne)
      refine ⟨c,?_,?_,?_⟩
      · simpa only [hja,hjb,runState] using hc
      · intro r
        change endpoint ((runState height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)).positioned.registry.bundles c) _=_
        rw [he]
        simp only [runLift,nextLift,
          FalseEdges.rowLift_other_xor s 0 a (by intro hh; exact ha0 (congrArg Fin.val hh))]
        congr 1
        change (crossed s height j h).positioned.registry.xors.embed a'.succ _ =
          (crossed s height j h).positioned.registry.xors.embed a _
        rw [ha]
      · intro r
        simpa only [runState,runFresh,dite_eq_right hlt,hindex] using hf r

open PlanarSatAssembly
variable {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

/-- Both boundary maps of a final residual interval, with the actual global
placement names. No assumed semantic or geometric edge interface remains. -/
theorem permutation_residual_bundle (i j : Fin (3 *m)) (lower : Bool)
    (hj : if lower then SatCrossingRetirement.Segments.FirstInColumn p i j
      else SatCrossingRetirement.Segments.LastInColumn p i j) :
    ∃ b : (PermutationGraph.finalState φ p).BundleId,
      (∀ r, endpoint ((PermutationGraph.finalState φ p).positioned.registry.bundles b)
        (boundarySlot lower r)=PermutationWirePlacement.vertex φ p
          (.inl (i,xorEndpoint (boundarySlot lower r)))) ∧
      (∀ r, endpoint ((PermutationGraph.finalState φ p).positioned.registry.bundles b)
        (boundarySlot (!lower) r)=PermutationWirePlacement.fresh φ p
          ⟨(i,j),by cases lower <;> exact hj.1⟩ (boundaryPort (!lower) r)) := by
  have hact : SatCrossingRouting.Active p i j := by cases lower <;> exact hj.1
  have hmem := (SatCrossingHorizontal.request_iff_active p i j).mpr hact
  let t : Fin (requests (permutationHeight p) j.val).length :=
    ⟨(requests (permutationHeight p) j.val).idxOf i.val,List.idxOf_lt_length_of_mem hmem⟩
  have ht : (requests (permutationHeight p) j.val)[t.val]=i.val := List.getElem_idxOf t.isLt
  have hheight : permutationHeight p (0+j.val)<permutationHeight p (0+i.val) := by
    simpa only [Nat.zero_add,permutationHeight_apply] using Nat.add_lt_add_right hact.2 1
  obtain ⟨b,hb,he,hf⟩ := run_residual_bundle (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    i j hact.1 lower hheight ⟨t.val,by simpa only [Nat.zero_add] using t.isLt⟩
    (by simpa only [Nat.zero_add] using ht) (by
      intro k hik hk hkj
      let k' : Fin (3*m) := ⟨k,by omega⟩
      have hh := extremum_separated p i j lower hj k'
        (by change i.val<k; omega) (by intro hh; exact hkj (by simpa using congrArg Fin.val hh))
      simpa only [Nat.zero_add] using hh)
  refine ⟨b,?_,?_⟩
  · intro r
    rw [PermutationWirePlacement.vertex_original]
    exact he r
  · intro r
    rw [rowIndex_eq_crossing p i j hact t ht] at hf
    exact hf r

/-- The upper residual arc has the alternating lane orientation used by the
retirement drawing. -/
theorem permutation_above (i j : Fin (3 *m))
    (hj : SatCrossingRetirement.Segments.LastInColumn p i j) (r : Fin 4) :
    (PermutationGraph.graph φ p).adj
      (if r.val%2=0 then PermutationWirePlacement.vertex φ p
          (.inl (i,SatCrossingRetirement.falseVertex r))
        else PermutationWirePlacement.fresh φ p ⟨(i,j),hj.1⟩
          ⟨outputPort 4 (.inr r),trivial⟩)
      (if r.val%2=0 then PermutationWirePlacement.fresh φ p ⟨(i,j),hj.1⟩
          ⟨inputPort 4 (.inr r),trivial⟩
        else PermutationWirePlacement.vertex φ p
          (.inl (i,SatCrossingRetirement.falseVertex r))) := by
  obtain ⟨b,he,hf⟩ := permutation_residual_bundle φ p i j false hj
  have hh := boundary_edge (PermutationGraph.finalState φ p) b r
  fin_cases r <;> norm_num only [Fin.reduceFinMk,Nat.reduceMod,Nat.reduceEqDiff,
    decide_true,decide_false,ite_true,ite_false] at hh ⊢
  all_goals
    simp only [Bool.not_false] at hf
    rw [he,hf] at hh
    exact hh

/-- The lower residual arc, again with its actual directed endpoint order. -/
theorem permutation_below (i j : Fin (3 *m))
    (hj : SatCrossingRetirement.Segments.FirstInColumn p i j) (r : Fin 4) :
    (PermutationGraph.graph φ p).adj
      (if r.val%2=0 then PermutationWirePlacement.fresh φ p ⟨(i,j),hj.1⟩
          ⟨outputPort 4 (.inr r),trivial⟩
        else PermutationWirePlacement.vertex φ p
          (.inl (i,SatCrossingRetirement.trueVertex r)))
      (if r.val%2=0 then PermutationWirePlacement.vertex φ p
          (.inl (i,SatCrossingRetirement.trueVertex r))
        else PermutationWirePlacement.fresh φ p ⟨(i,j),hj.1⟩
          ⟨inputPort 4 (.inr r),trivial⟩) := by
  obtain ⟨b,he,hf⟩ := permutation_residual_bundle φ p i j true hj
  have hh := boundary_edge (PermutationGraph.finalState φ p) b r
  fin_cases r <;> norm_num only [Fin.reduceFinMk,Nat.reduceMod,Nat.reduceEqDiff,
    decide_true,decide_false,ite_true,ite_false] at hh ⊢
  all_goals
    simp only [Bool.not_true] at hf
    rw [he,hf] at hh
    exact hh

end GridHardness.CorrectedSatInterval.ResidualEdges
