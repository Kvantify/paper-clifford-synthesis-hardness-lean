/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalVerticalSpans

/-!
# Corrected SAT Interval Vertical Pairs

Two crossings consecutive in geometric height determine an actual final
registered bundle, regardless of their chronological order. The proof first
tracks a spanning interval to the earlier request and then tracks its new
anchored endpoint to the later request.
-/

public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering HorizontalEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem spans_run_pair (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j)
      (line low high : Nat) (_hord : low<high) (lower : Bool)
      (_hspan : Spans s line low high) (a b : Fin n) (_hab : a<b)
      (ta : Fin (requests height (j+a.val)).length)
      (tb : Fin (requests height (j+b.val)).length),
      (requests height (j+a.val))[ta.val]=line →
      (requests height (j+b.val))[tb.val]=line →
      height (j+a.val)=(if lower then low else high) →
      height (j+b.val)=(if lower then high else low) →
      (∀ k, j≤k → k<j+n → k≠j+a.val → k≠j+b.val → height k<low ∨ high<height k) →
      ∃ c : (runState height hinj hpos n j s h).BundleId,
        (runState height hinj hpos n j s h).positioned.segments c=⟨line,low,high⟩ ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c)
            (boundarySlot lower r)=runFresh height hinj hpos n j s h
              (rowIndex height n j a ta) (boundaryPort lower r)) ∧
        (∀ r, endpoint ((runState height hinj hpos n j s h).positioned.registry.bundles c)
            (boundarySlot (!lower) r)=runFresh height hinj hpos n j s h
              (rowIndex height n j b tb) (boundaryPort (!lower) r)) := by
  induction n with
  | zero => intro j s h line low high hord lower hspan a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h line low high hord lower hspan a b hab ta tb hta htb hfirst hsecond hgap
    have hb0 : b.val≠0 := by have : a.val<b.val := hab; omega
    let b' : Fin n := ⟨b.val-1,by have := b.isLt; omega⟩
    have hjb : j+1+b'.val=j+b.val := by dsimp [b']; omega
    let tb' : Fin (requests height (j+1+b'.val)).length :=
      ⟨tb.val,by simpa only [hjb] using tb.isLt⟩
    have hidxb := rowIndex_succ height n j b hb0 tb
    have hidxb' : (rowIndex height (n+1) j b tb).val=
        (rowIndex height n (j+1) b' tb').val+(requests height j).length := hidxb
    have hltb : ¬(rowIndex height (n+1) j b tb).val<(requests height j).length := by omega
    have hindexb : (⟨(rowIndex height (n+1) j b tb).val-(requests height j).length,
        by have := (rowIndex height (n+1) j b tb).isLt
           simp only [moveCount] at this
           omega⟩ : Fin (moveCount height n (j+1)))=rowIndex height n (j+1) b' tb' := by
      apply Fin.ext
      dsimp only [Fin.val_mk]
      omega
    by_cases ha0 : a.val=0
    · have ha' : a=0 := Fin.ext ha0
      subst a
      have hanchor : Anchored (next s height j h) line low high lower
          (fun r => rowFresh s 0 (height j) (requests height j)
            (requests_nodup height j) h.requests_covered
            ⟨ta.val,ta.isLt⟩ (boundaryPort lower r)) := by
        apply anchored_retire
        exact spans_row_anchored s 0 line low high hord lower hspan (height j)
          (by simpa using hfirst) (requests height j) (requests_nodup height j)
          h.requests_covered ⟨ta.val,ta.isLt⟩ (by simpa using hta)
      obtain ⟨c,hc,he,hf⟩ := anchored_run_connect height hinj hpos n (j+1)
        (next s height j h) (next_ready s height hinj hpos j h) line low high hord lower
        _ hanchor b' tb' (by simpa only [hjb,tb'] using htb)
        (by simpa only [hjb] using hsecond)
        (fun k hk hkn hne => hgap k (by omega) (by omega) (by simp; omega)
          (by simpa only [hjb] using hne))
      refine ⟨c,hc,?_,?_⟩
      · intro r
        simp only [runFresh,rowIndex_zero,
          show ta.val<(requests height j).length from ta.isLt,↓reduceDIte]
        exact he r
      · intro r
        simp only [runFresh,dite_eq_right hltb,hindexb]
        exact hf r
    · let a' : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hja : j+1+a'.val=j+a.val := by dsimp [a']; omega
      let ta' : Fin (requests height (j+1+a'.val)).length :=
        ⟨ta.val,by simpa only [hja] using ta.isLt⟩
      have hspan' : Spans (next s height j h) line low high := by
        apply spans_retire
        exact spans_row s 0 line low high hspan (height j) (requests height j)
          (requests_nodup height j) h.requests_covered
          (fun i _ => Or.inr (hgap j le_rfl (by omega) (by omega) (by omega)))
      obtain ⟨c,hc,he,hf⟩ := ih (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) line low high hord lower hspan' a' b'
        (by change a.val-1<b.val-1; have : a.val<b.val := hab; omega)
        ta' tb' (by simpa only [hja,ta'] using hta) (by simpa only [hjb,tb'] using htb)
        (by simpa only [hja] using hfirst) (by simpa only [hjb] using hsecond)
        (fun k hk hkn hka hkb => hgap k (by omega) (by omega)
          (by simpa only [←hja] using hka) (by simpa only [←hjb] using hkb))
      refine ⟨c,hc,?_,?_⟩
      · intro r
        have hidxa := rowIndex_succ height n j a ha0 ta
        have hidxa' : (rowIndex height (n+1) j a ta).val=
            (rowIndex height n (j+1) a' ta').val+(requests height j).length := hidxa
        have hlta : ¬(rowIndex height (n+1) j a ta).val<(requests height j).length := by omega
        have hindexa : (⟨(rowIndex height (n+1) j a ta).val-(requests height j).length,
            by have := (rowIndex height (n+1) j a ta).isLt
               simp only [moveCount] at this
               omega⟩ : Fin (moveCount height n (j+1)))=rowIndex height n (j+1) a' ta' := by
          apply Fin.ext
          dsimp only [Fin.val_mk]
          omega
        simp only [runFresh,dite_eq_right hlta,hindexa]
        exact he r
      · intro r
        simp only [runFresh,dite_eq_right hltb,hindexb]
        exact hf r

end GridHardness.CorrectedSatInterval.VerticalEdges
