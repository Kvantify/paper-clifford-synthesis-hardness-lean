/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetainedEdges
public import GridHardness.SatCrossingHorizontalCatalogue

/-!
# Corrected SAT Interval Horizontal Edges

Consecutive crossings on one horizontal wire have two directed connector
arcs. Their endpoints are the retained vertices allocated by the actual sweep,
and both arcs persist through all subsequent requests and retirements.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.HorizontalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev RetainedVertex := SatCrossingHorizontal.RetainedVertex

def oldPort (b : Bool) : RetainedVertex := ⟨row 0 b,trivial⟩
def newPort (b : Bool) : RetainedVertex := FalseEdges.retainedPort (!b)

theorem old_direction (b : Bool) : RetainedEdges.Direction b (oldPort b) := by
  cases b
  · exact RetainedEdges.input_direction 0
  · exact RetainedEdges.output_direction 0

theorem new_direction (b incoming : Bool) : RetainedEdges.Direction incoming (newPort b) := by
  cases b <;> intro i t he <;> cases he

variable {n : Nat}

theorem crossLift_latest (s : IntervalState n) (a : Fin n) (i height : Nat)
    (hc : s.Covered i height) (k nextHeight : Nat)
    (hk : (s.cross a i height hc).Covered k nextHeight) (u : RetainedVertex) :
    crossLift (s.cross a i height hc) a k nextHeight hk (.inr u.val)=
      Horizontal.kept s a i height hc k nextHeight hk u := by
  let o : Boundary.Outside (s.cross a i height hc) a := ⟨.inr u.val,by
    rintro ⟨j,hj⟩
    rw [Horizontal.latest_active] at hj
    exact SatCrossingHorizontal.retained_ne_zero u j (Sum.inr.inj hj)⟩
  exact crossLift_survivor _ _ _ _ _ o

theorem row_incoming (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Nat) (ht : t +1<rs.length) :
    (s.crossRequests a height rs hn hc).adj
      (rowFresh s a height rs hn hc ⟨t,by omega⟩ (oldPort false))
      (rowFresh s a height rs hn hc ⟨t+1,ht⟩ (newPort false)) := by
  induction rs generalizing s t with
  | nil => simp at ht
  | cons i is ih =>
    by_cases ht0 : t=0
    · subst t
      cases is with
      | nil => simp at ht
      | cons k ks =>
        have hki : k≠i := by
          intro he
          exact (List.nodup_cons.mp hn).1 (by simp [he])
        simp only [rowFresh,show ¬(0+1=0) by omega,
          ↓reduceDIte,Nat.add_sub_cancel]
        change (s.crossRequests a height (i::k::ks) hn hc).adj
          (rowLift ((s.cross a i height _).cross a k height _) a height ks _ _
            (crossLift (s.cross a i height _) a k height _ (.inr (oldPort false).val)))
          (rowLift ((s.cross a i height _).cross a k height _) a height ks _ _
            (.inr (newPort false).val))
        apply (TrueEdges.row_adj _ _ _ _ _ _ _ _
          (TrueEdges.cross_safe _ _ _ _ _ false _
            (RetainedEdges.cross_safe _ _ _ _ _ false _ (old_direction false)))
          (RetainedEdges.cross_safe _ _ _ _ _ true _ (new_direction false true))).mpr
        rw [crossLift_latest]
        exact (Horizontal.incoming_interface _ _ _ _ _ _ _ _ hki _ _).mpr ⟨rfl,rfl⟩
    · simp only [rowFresh,dite_eq_right ht0,
        show ¬(t+1=0) by omega,↓reduceDIte]
      have hh := ih (s.cross a i height _) (List.nodup_cons.mp hn).2
        (s.cross_remaining_covered a height i is hn hc) (t-1)
        (by simp only [List.length_cons] at ht; omega)
      convert hh using 1 <;> congr 1
      all_goals (apply Fin.ext; dsimp; omega)

theorem row_outgoing (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Nat) (ht : t +1<rs.length) :
    (s.crossRequests a height rs hn hc).adj
      (rowFresh s a height rs hn hc ⟨t+1,ht⟩ (newPort true))
      (rowFresh s a height rs hn hc ⟨t,by omega⟩ (oldPort true)) := by
  induction rs generalizing s t with
  | nil => simp at ht
  | cons i is ih =>
    by_cases ht0 : t=0
    · subst t
      cases is with
      | nil => simp at ht
      | cons k ks =>
        have hki : k≠i := by
          intro he
          exact (List.nodup_cons.mp hn).1 (by simp [he])
        simp only [rowFresh,show ¬(0+1=0) by omega,
          ↓reduceDIte,Nat.add_sub_cancel]
        change (s.crossRequests a height (i::k::ks) hn hc).adj
          (rowLift ((s.cross a i height _).cross a k height _) a height ks _ _
            (.inr (newPort true).val))
          (rowLift ((s.cross a i height _).cross a k height _) a height ks _ _
            (crossLift (s.cross a i height _) a k height _ (.inr (oldPort true).val)))
        apply (TrueEdges.row_adj _ _ _ _ _ _ _ _
          (RetainedEdges.cross_safe _ _ _ _ _ false _ (new_direction true false))
          (TrueEdges.cross_safe _ _ _ _ _ true _
            (RetainedEdges.cross_safe _ _ _ _ _ true _ (old_direction true)))).mpr
        rw [crossLift_latest]
        exact (Horizontal.outgoing_interface _ _ _ _ _ _ _ _ hki _ _).mpr ⟨rfl,rfl⟩
    · simp only [rowFresh,dite_eq_right ht0,
        show ¬(t+1=0) by omega,↓reduceDIte]
      have hh := ih (s.cross a i height _) (List.nodup_cons.mp hn).2
        (s.cross_remaining_covered a height i is hn hc) (t-1)
        (by simp only [List.length_cons] at ht; omega)
      convert hh using 1 <;> congr 1
      all_goals (apply Fin.ext; dsimp; omega)

/-- Chronological allocation index of a specified request in a specified row. -/
def rowIndex (height : Nat → Nat) (n j : Nat) (a : Fin n)
    (t : Fin (requests height (j +a.val)).length) : Fin (moveCount height n j) :=
  ⟨(trace height n j).idxOf ((requests height (j+a.val))[t.val],j+a.val),by
    rw [←trace_length]
    apply List.idxOf_lt_length_of_mem
    have hm := (mem_requests height _ (j+a.val)).mp (List.getElem_mem t.isLt)
    exact (mem_trace height n j _).mpr
      ⟨hm.1,hm.2,by omega,by have := a.isLt; omega⟩⟩

theorem rowIndex_zero (height : Nat → Nat) (n j : Nat)
    (t : Fin (requests height j).length) :
    (rowIndex height (n+1) j 0 t).val=t.val := by
  change (trace height (n+1) j).idxOf ((requests height j)[t.val],j)=t.val
  have hm : ((requests height j)[t.val],j)∈(requests height j).map (fun i => (i,j)) :=
    List.mem_map.mpr ⟨_,List.getElem_mem t.isLt,rfl⟩
  rw [trace,List.idxOf_append_of_mem hm]
  have hn : ((requests height j).map (fun i => (i,j))).Nodup :=
    List.Nodup.map_on (fun _ _ _ _ he => (Prod.mk.inj he).1) (requests_nodup height j)
  have hh := hn.idxOf_getElem t.val (by simpa only [List.length_map] using t.isLt)
  rw [List.getElem_map (fun i => (i,j))] at hh
  exact hh

theorem rowIndex_succ (height : Nat → Nat) (n j : Nat) (a : Fin (n +1))
    (ha : a.val ≠0) (t : Fin (requests height (j +a.val)).length) :
    (rowIndex height (n+1) j a t).val=
      (rowIndex height n (j+1) ⟨a.val-1,by have := a.isLt; omega⟩
        ⟨t.val,by simpa only [show j+1+(a.val-1)=j+a.val by omega] using t.isLt⟩).val+
      (requests height j).length := by
  simp only [rowIndex,Fin.val_mk,show j+1+(a.val-1)=j+a.val by omega]
  exact FalseEdges.firstIndex_succ height n j _ a.val (by omega)

theorem run_incoming (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (t : Nat) (ht : t+1<(requests height (j+a.val)).length),
      (runState height hinj hpos n j s h).adj
        (runFresh height hinj hpos n j s h
          (rowIndex height n j a ⟨t,by omega⟩) (oldPort false))
        (runFresh height hinj hpos n j s h
          (rowIndex height n j a ⟨t+1,ht⟩) (newPort false)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a t ht
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have ht' : t+1<(requests height j).length := by simpa using ht
      simp only [runFresh,rowIndex_zero,show t<(requests height j).length by omega,
        show t+1<(requests height j).length from ht',↓reduceDIte]
      apply (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (TrueEdges.retire_safe _ _ _ _ false _
          (RetainedEdges.rowFresh_safe _ _ _ _ _ _ _ false _ (old_direction false)))
        (TrueEdges.retire_safe _ _ _ _ true _
          (RetainedEdges.rowFresh_safe _ _ _ _ _ _ _ true _ (new_direction false true)))).mpr
      exact row_incoming s 0 (height j) _ _ _ t ht'
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have ht' : t+1<(requests height (j+1+b.val)).length := by simpa only [hj] using ht
      have h0 := rowIndex_succ height n j a ha ⟨t,by omega⟩
      have h1 := rowIndex_succ height n j a ha ⟨t+1,ht⟩
      have hn0 : ¬(rowIndex height (n+1) j a ⟨t,by omega⟩).val<
          (requests height j).length := by omega
      have hn1 : ¬(rowIndex height (n+1) j a ⟨t+1,ht⟩).val<
          (requests height j).length := by omega
      simp only [runFresh,dite_eq_right hn0,dite_eq_right hn1]
      convert ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b t ht' using 1 <;>
        congr 1 <;> apply Fin.ext <;> dsimp only [Fin.val_mk,b] at * <;> omega

theorem run_outgoing (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (t : Nat) (ht : t+1<(requests height (j+a.val)).length),
      (runState height hinj hpos n j s h).adj
        (runFresh height hinj hpos n j s h
          (rowIndex height n j a ⟨t+1,ht⟩) (newPort true))
        (runFresh height hinj hpos n j s h
          (rowIndex height n j a ⟨t,by omega⟩) (oldPort true)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a t ht
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have ht' : t+1<(requests height j).length := by simpa using ht
      simp only [runFresh,rowIndex_zero,show t<(requests height j).length by omega,
        show t+1<(requests height j).length from ht',↓reduceDIte]
      apply (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (TrueEdges.retire_safe _ _ _ _ false _
          (RetainedEdges.rowFresh_safe _ _ _ _ _ _ _ false _ (new_direction true false)))
        (TrueEdges.retire_safe _ _ _ _ true _
          (RetainedEdges.rowFresh_safe _ _ _ _ _ _ _ true _ (old_direction true)))).mpr
      exact row_outgoing s 0 (height j) _ _ _ t ht'
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have ht' : t+1<(requests height (j+1+b.val)).length := by simpa only [hj] using ht
      have h0 := rowIndex_succ height n j a ha ⟨t,by omega⟩
      have h1 := rowIndex_succ height n j a ha ⟨t+1,ht⟩
      have hn0 : ¬(rowIndex height (n+1) j a ⟨t,by omega⟩).val<
          (requests height j).length := by omega
      have hn1 : ¬(rowIndex height (n+1) j a ⟨t+1,ht⟩).val<
          (requests height j).length := by omega
      simp only [runFresh,dite_eq_right hn0,dite_eq_right hn1]
      convert ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b t ht' using 1 <;>
        congr 1 <;> apply Fin.ext <;> dsimp only [Fin.val_mk,b] at * <;> omega

/-- Geometric consecutive columns are consecutive entries of the actual,
increasing request list. -/
theorem consecutive_request_indices {N : Nat} (p : Equiv.Perm (Fin N))
    (i k j : Fin N) (hc : SatCrossingHorizontal.ConsecutiveColumns p i k j) :
    ∃ t, ∃ ht : t+1<(requests (permutationHeight p) j.val).length,
      (requests (permutationHeight p) j.val)[t]'(by omega)=i.val ∧
      (requests (permutationHeight p) j.val)[t+1]'ht=k.val := by
  let rs := requests (permutationHeight p) j.val
  have hi : i.val∈rs := (SatCrossingHorizontal.request_iff_active p i j).mpr hc.1
  have hk : k.val∈rs := (SatCrossingHorizontal.request_iff_active p k j).mpr hc.2.1
  have hi' := List.idxOf_lt_length_of_mem hi
  have hk' := List.idxOf_lt_length_of_mem hk
  have hei := List.getElem_idxOf hi'
  have hek := List.getElem_idxOf hk'
  have hs := List.pairwise_iff_getElem.mp (requests_increasing (permutationHeight p) j.val)
  have hik : rs.idxOf i.val < rs.idxOf k.val := by
    by_contra hh
    rcases lt_or_eq_of_le (Nat.le_of_not_gt hh) with hl | he
    · have hlt := hs _ _ hk' hi' hl
      rw [hek,hei] at hlt
      have hh := hc.2.2.1
      exact (not_lt_of_ge (Nat.le_of_lt hh)) hlt
    · have he' : i.val=k.val := by
        have hh : rs[rs.idxOf k.val]=i.val := by simpa only [he] using hei
        exact hh.symm.trans hek
      have hh := hc.2.2.1
      exact (ne_of_lt hh) (Fin.ext he')
  have hnext : rs.idxOf k.val=rs.idxOf i.val+1 := by
    by_contra hh
    have hb : rs.idxOf i.val+1<rs.length := by omega
    have hmid := List.getElem_mem hb
    have hm := (mem_requests (permutationHeight p) _ j.val).mp hmid
    let a : Fin N := ⟨rs[rs.idxOf i.val+1],by have := j.isLt; omega⟩
    have hia : i<a := by
      have hh := hs _ _ hi' hb (by omega)
      rw [hei] at hh
      exact hh
    have hak : a<k := by
      have hh := hs _ _ hb hk' (by omega)
      rw [hek] at hh
      exact hh
    have ha : SatCrossingRouting.Active p a j :=
      (SatCrossingHorizontal.request_iff_active p a j).mp hmid
    exact (not_lt_of_ge (hc.2.2.2 a ha hia)) hak
  have hbound : rs.idxOf i.val+1<rs.length := by omega
  refine ⟨rs.idxOf i.val,hbound,hei,?_⟩
  simpa only [←hnext] using hek

open PlanarSatAssembly
variable {m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

theorem rowIndex_eq_crossing (i j : Fin (3 *m)) (hc : SatCrossingRouting.Active p i j)
    (t : Fin (requests (permutationHeight p) j.val).length)
    (ht : (requests (permutationHeight p) j.val)[t.val] =i.val) :
    rowIndex (permutationHeight p) (3*m) 0 j
      ⟨t.val,by simpa only [Nat.zero_add] using t.isLt⟩=
      (PermutationWirePlacement.crossingEquiv p).symm ⟨(i,j),hc⟩ := by
  apply Fin.ext
  rw [PermutationWirePlacement.crossingEquiv_symm_val]
  simpa only [rowIndex,Fin.val_mk,Nat.zero_add] using
    congrArg (fun u => (trace (permutationHeight p) (3*m) 0).idxOf (u,j.val)) ht

/-- The upper horizontal connector is a final-graph arc, with the exact
retained endpoint names used by the lattice drawing. -/
theorem permutation_incoming (i k j : Fin (3 *m))
    (hc : SatCrossingHorizontal.ConsecutiveColumns p i k j) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.fresh φ p ⟨(i,j),hc.1⟩ (oldPort false))
      (PermutationWirePlacement.fresh φ p ⟨(k,j),hc.2.1⟩ (newPort false)) := by
  obtain ⟨t,ht,hi,hk⟩ := consecutive_request_indices p i k j hc
  have he := run_incoming (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j t (by simpa using ht)
  rw [rowIndex_eq_crossing p i j hc.1 ⟨t,by omega⟩ hi,
    rowIndex_eq_crossing p k j hc.2.1 ⟨t+1,ht⟩ hk] at he
  exact he

/-- The lower connector runs in the opposite direction and survives the same
complete sweep. No bundle-safety or naming assumptions remain. -/
theorem permutation_outgoing (i k j : Fin (3 *m))
    (hc : SatCrossingHorizontal.ConsecutiveColumns p i k j) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.fresh φ p ⟨(k,j),hc.2.1⟩ (newPort true))
      (PermutationWirePlacement.fresh φ p ⟨(i,j),hc.1⟩ (oldPort true)) := by
  obtain ⟨t,ht,hi,hk⟩ := consecutive_request_indices p i k j hc
  have he := run_outgoing (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j t (by simpa using ht)
  rw [rowIndex_eq_crossing p i j hc.1 ⟨t,by omega⟩ hi,
    rowIndex_eq_crossing p k j hc.2.1 ⟨t+1,ht⟩ hk] at he
  exact he

end GridHardness.CorrectedSatInterval.HorizontalEdges
