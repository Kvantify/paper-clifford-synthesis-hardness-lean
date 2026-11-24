/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalVerticalPairs

/-!
# Corrected SAT Interval Vertical Permutation

Actual final arcs between consecutive vertical crossings, for every
occurrence permutation. The proof starts at the original wire's retirement,
tracks the two crossing heights through the changing interval registry, and
identifies their final retained vertex names.
-/

public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering HorizontalEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Removing the first sweep row preserves the chronological name of every
later crossing, with the expected offset in its row index. -/
theorem runFresh_row_succ (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n j : Nat) (s : IntervalState (n +1)) (h : Ready s height j)
    (a : Fin (n +1)) (ha : a.val ≠0) (t : Fin (requests height (j +a.val)).length)
    (v : SatCrossingHorizontal.RetainedVertex) :
    runFresh height hinj hpos (n+1) j s h (rowIndex height (n+1) j a t) v=
      runFresh height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)
        (rowIndex height n (j+1) ⟨a.val-1,by have := a.isLt; omega⟩
          ⟨t.val,by simpa only [show j+1+(a.val-1)=j+a.val by omega] using t.isLt⟩) v := by
  have hi := rowIndex_succ height n j a ha t
  have hn : ¬(rowIndex height (n+1) j a t).val<(requests height j).length := by omega
  simp only [runFresh,dite_eq_right hn]
  congr 1
  apply Fin.ext
  dsimp only [Fin.val_mk]
  omega

/-- Beginning before the original column has retired, follow both later
crossing names into one exact final interval. -/
theorem run_retirement_pair (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a b c : Fin n),
      a<b → b<c →
      ∀ (low high : Nat), low<high → 0<low → high<height (j+a.val) →
      ∀ (lower : Bool) (t : Fin (requests height (j+b.val)).length)
        (u : Fin (requests height (j+c.val)).length),
      (requests height (j+b.val))[t.val]=j+a.val →
      (requests height (j+c.val))[u.val]=j+a.val →
      height (j+b.val)=(if lower then low else high) →
      height (j+c.val)=(if lower then high else low) →
      (∀ k, j+a.val<k → k<j+n → k≠j+b.val → k≠j+c.val →
        height k<low ∨ high<height k) →
      ∃ d : (runState height hinj hpos n j s h).BundleId,
        (runState height hinj hpos n j s h).positioned.segments d=⟨j+a.val,low,high⟩ ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles d)
          (boundarySlot lower r)=runFresh height hinj hpos n j s h
            (rowIndex height n j b t) (boundaryPort lower r)) ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles d)
          (boundarySlot (!lower) r)=runFresh height hinj hpos n j s h
            (rowIndex height n j c u) (boundaryPort (!lower) r)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a b c hab hbc low high hord hlo hhi lower t u ht hu hbheight hcheight hgap
    have hb0 : b.val≠0 := by have : a.val<b.val := hab; omega
    have hc0 : c.val≠0 := by have : b.val<c.val := hbc; omega
    let b' : Fin n := ⟨b.val-1,by have := b.isLt; omega⟩
    let c' : Fin n := ⟨c.val-1,by have := c.isLt; omega⟩
    have hjb : j+1+b'.val=j+b.val := by dsimp [b']; omega
    have hjc : j+1+c'.val=j+c.val := by dsimp [c']; omega
    let t' : Fin (requests height (j+1+b'.val)).length :=
      ⟨t.val,by simpa only [hjb] using t.isLt⟩
    let u' : Fin (requests height (j+1+c'.val)).length :=
      ⟨u.val,by simpa only [hjc] using u.isLt⟩
    have hbc' : b'<c' := by
      change b.val-1<c.val-1
      have : b.val<c.val := hbc
      omega
    by_cases ha0 : a.val=0
    · have ha' : a=0 := Fin.ext ha0
      subst a
      obtain ⟨d,hd,he,hf⟩ := spans_run_pair height hinj hpos n (j+1)
        (next s height j h) (next_ready s height hinj hpos j h) j low high hord lower
        (show Spans (next s height j h) j low high from
          ⟨none,rfl,hlo,by change high<height j; simpa only [Fin.val_zero,Nat.add_zero] using hhi⟩)
        b' c' hbc' t' u'
        (by simpa only [hjb,t',Fin.val_mk,Fin.val_zero,Nat.add_zero] using ht)
        (by simpa only [hjc,u',Fin.val_mk,Fin.val_zero,Nat.add_zero] using hu)
        (by simpa only [hjb] using hbheight)
        (by simpa only [hjc] using hcheight)
        (by
          intro k hk hkn hkb hkc
          exact hgap k (by simpa using hk) (by omega)
            (by simpa only [hjb] using hkb) (by simpa only [hjc] using hkc))
      refine ⟨d,?_,?_,?_⟩
      · simpa only [Fin.val_zero,Nat.add_zero,runState] using hd
      · intro r
        simpa only [runState,runFresh_row_succ height hinj hpos n j s h b hb0] using he r
      · intro r
        simpa only [runState,runFresh_row_succ height hinj hpos n j s h c hc0] using hf r
    · let a' : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hja : j+1+a'.val=j+a.val := by dsimp [a']; omega
      have hab' : a'<b' := by
        change a.val-1<b.val-1
        have : a.val<b.val := hab
        omega
      obtain ⟨d,hd,he,hf⟩ := ih (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) a' b' c' hab' hbc' low high hord hlo
        (by simpa only [hja] using hhi) lower t' u'
        (by simpa only [hja,hjb,t',Fin.val_mk] using ht)
        (by simpa only [hja,hjc,u',Fin.val_mk] using hu)
        (by simpa only [hjb] using hbheight)
        (by simpa only [hjc] using hcheight)
        (by
          intro k hk hkn hkb hkc
          rw [hja] at hk
          exact hgap k hk (by omega)
            (by simpa only [hjb] using hkb) (by simpa only [hjc] using hkc))
      refine ⟨d,?_,?_,?_⟩
      · simpa only [hja,runState] using hd
      · intro r
        simpa only [runState,runFresh_row_succ height hinj hpos n j s h b hb0] using he r
      · intro r
        simpa only [runState,runFresh_row_succ height hinj hpos n j s h c hc0] using hf r

/-- Every other later row is outside the closed gap between consecutive
active crossing heights. -/
theorem consecutive_separated {N : Nat} (p : Equiv.Perm (Fin N)) (i j k : Fin N)
    (hc : SatCrossingRouting.Consecutive p i j k) (l : Fin N)
    (hil : i <l) (hlj : l ≠j) (hlk : l ≠k) :
    permutationHeight p l.val<permutationHeight p j.val ∨
      permutationHeight p k.val<permutationHeight p l.val := by
  have hlj' : p l≠p j := fun hh => hlj (p.injective hh)
  have hlk' : p k≠p l := fun hh => hlk (p.injective hh).symm
  by_cases hact : SatCrossingRouting.Active p i l
  · by_cases hh : p j<p l
    · have hlt : p k<p l := lt_of_le_of_ne (hc.2.2.2 l hact hh) hlk'
      right
      simpa only [permutationHeight_apply] using Nat.add_lt_add_right hlt 1
    · have hlt : p l<p j := lt_of_le_of_ne (le_of_not_gt hh) hlj'
      left
      simpa only [permutationHeight_apply] using Nat.add_lt_add_right hlt 1
  · have hle : p i≤p l := le_of_not_gt (fun hh => hact ⟨hil,hh⟩)
    have hlt : p k<p l := hc.2.1.2.trans_le hle
    right
    simpa only [permutationHeight_apply] using Nat.add_lt_add_right hlt 1

open PlanarSatAssembly
variable {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

/-- A consecutive pair of crossing heights determines a final registered
bundle with the exact retained crossing vertices at both ends. -/
theorem permutation_vertical_bundle (i j k : Fin (3 *m))
    (hc : SatCrossingRouting.Consecutive p i j k) :
    ∃ b : (PermutationGraph.finalState φ p).BundleId,
      (∀ r, endpoint ((PermutationGraph.finalState φ p).positioned.registry.bundles b)
        (boundarySlot true r)=PermutationWirePlacement.fresh φ p
          ⟨(i,j),hc.1⟩ (boundaryPort true r)) ∧
      (∀ r, endpoint ((PermutationGraph.finalState φ p).positioned.registry.bundles b)
        (boundarySlot false r)=PermutationWirePlacement.fresh φ p
          ⟨(i,k),hc.2.1⟩ (boundaryPort false r)) := by
  have hjmem := (SatCrossingHorizontal.request_iff_active p i j).mpr hc.1
  have hkmem := (SatCrossingHorizontal.request_iff_active p i k).mpr hc.2.1
  let t : Fin (requests (permutationHeight p) j.val).length :=
    ⟨(requests (permutationHeight p) j.val).idxOf i.val,List.idxOf_lt_length_of_mem hjmem⟩
  let u : Fin (requests (permutationHeight p) k.val).length :=
    ⟨(requests (permutationHeight p) k.val).idxOf i.val,List.idxOf_lt_length_of_mem hkmem⟩
  have ht : (requests (permutationHeight p) j.val)[t.val]=i.val := List.getElem_idxOf t.isLt
  have hu : (requests (permutationHeight p) k.val)[u.val]=i.val := List.getElem_idxOf u.isLt
  have hord : permutationHeight p j.val<permutationHeight p k.val := by
    simpa only [permutationHeight_apply] using Nat.add_lt_add_right hc.2.2.1 1
  have hhi : permutationHeight p k.val<permutationHeight p (0+i.val) := by
    simpa only [Nat.zero_add,permutationHeight_apply] using Nat.add_lt_add_right hc.2.1.2 1
  have hgap : ∀ l, 0+i.val<l → l<0+3*m → l≠0+j.val → l≠0+k.val →
      permutationHeight p l<permutationHeight p j.val ∨
        permutationHeight p k.val<permutationHeight p l := by
    intro l hil hl hlj hlk
    let l' : Fin (3*m) := ⟨l,by omega⟩
    exact consecutive_separated p i j k hc l' (by change i.val<l; omega)
      (by intro he; exact hlj (by simpa only [Nat.zero_add] using congrArg Fin.val he))
      (by intro he; exact hlk (by simpa only [Nat.zero_add] using congrArg Fin.val he))
  have hne : j≠k := fun he => (ne_of_lt hc.2.2.1) (congrArg p he)
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · obtain ⟨b,hb,he,hf⟩ := run_retirement_pair (permutationHeight p) (permutationHeight_injective p)
      (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
      i j k hc.1.1 hjk (permutationHeight p j.val) (permutationHeight p k.val) hord
      (permutationHeight_pos p _) hhi true
      ⟨t.val,by simpa only [Nat.zero_add] using t.isLt⟩
      ⟨u.val,by simpa only [Nat.zero_add] using u.isLt⟩
      (by simpa only [Nat.zero_add] using ht) (by simpa only [Nat.zero_add] using hu)
      (by simp only [Nat.zero_add,ite_true]) (by simp only [Nat.zero_add,ite_true]) hgap
    rw [rowIndex_eq_crossing p i j hc.1 t ht] at he
    rw [rowIndex_eq_crossing p i k hc.2.1 u hu] at hf
    exact ⟨b,he,hf⟩
  · obtain ⟨b,hb,he,hf⟩ := run_retirement_pair (permutationHeight p) (permutationHeight_injective p)
      (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
      i k j hc.2.1.1 hkj (permutationHeight p j.val) (permutationHeight p k.val) hord
      (permutationHeight_pos p _) hhi false
      ⟨u.val,by simpa only [Nat.zero_add] using u.isLt⟩
      ⟨t.val,by simpa only [Nat.zero_add] using t.isLt⟩
      (by simpa only [Nat.zero_add] using hu) (by simpa only [Nat.zero_add] using ht)
      (by simp only [Nat.zero_add,Bool.false_eq_true,ite_false])
      (by simp only [Nat.zero_add,Bool.false_eq_true,ite_false]) (by intro l hil hl hlk hlj; exact hgap l hil hl hlj hlk)
    rw [rowIndex_eq_crossing p i k hc.2.1 u hu] at he
    rw [rowIndex_eq_crossing p i j hc.1 t ht] at hf
    exact ⟨b,hf,he⟩

/-- All four oriented connections between consecutive active crossing cells
are actual arcs of the final graph, independent of their processing order. -/
theorem permutation_vertical (i j k : Fin (3 *m))
    (hc : SatCrossingRouting.Consecutive p i j k) (r : Fin 4) :
    (PermutationGraph.graph φ p).adj
      (if r.val%2=0 then PermutationWirePlacement.fresh φ p ⟨(i,k),hc.2.1⟩
          ⟨outputPort 4 (.inr r),trivial⟩
        else PermutationWirePlacement.fresh φ p ⟨(i,j),hc.1⟩
          ⟨outputPort 4 (.inr r),trivial⟩)
      (if r.val%2=0 then PermutationWirePlacement.fresh φ p ⟨(i,j),hc.1⟩
          ⟨inputPort 4 (.inr r),trivial⟩
        else PermutationWirePlacement.fresh φ p ⟨(i,k),hc.2.1⟩
          ⟨inputPort 4 (.inr r),trivial⟩) := by
  obtain ⟨b,he,hf⟩ := permutation_vertical_bundle φ p i j k hc
  have hh := boundary_edge (PermutationGraph.finalState φ p) b r
  fin_cases r <;> norm_num only [Fin.reduceFinMk,Nat.reduceMod,Nat.reduceEqDiff,
    decide_true,decide_false,ite_true,ite_false] at hh ⊢
  all_goals
    rw [he,hf] at hh
    exact hh

end GridHardness.CorrectedSatInterval.VerticalEdges
