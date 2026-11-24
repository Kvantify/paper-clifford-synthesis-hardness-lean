/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetiredSideEdges

/-!
# Corrected SAT Interval Last Links

The last crossing of an occurrence row retains two links to the
false side of the retired XOR. Their final endpoints use the actual
chronological fresh names and the original occurrence-XOR names.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.LastLinks
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def rowPort (b : Bool) : SatCrossingHorizontal.RetainedVertex := ⟨row 0 b,trivial⟩

variable {n : Nat}

theorem row_incoming (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (ht : t.val +1=rs.length) :
    (s.crossRequests a height rs hn hc).adj (rowFresh s a height rs hn hc t (rowPort false))
      ((s.crossRequests a height rs hn hc).positioned.registry.xors.embed a 4) := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    cases is with
    | nil =>
      have ht0 : t.val=0 := by simp only [List.length_cons,List.length_nil] at ht; omega
      simp only [rowFresh,dite_eq_left ht0,rowLift,IntervalState.crossRequests]
      rw [Horizontal.latest_active]
      change Adj 4 (row 0 false) (x 0 4)
      decide +kernel
    | cons k ks =>
      have ht0 : t.val≠0 := by simp only [List.length_cons] at ht; omega
      let t' : Fin (k::ks).length := ⟨t.val-1,by
        simp only [List.length_cons] at ht ⊢
        omega⟩
      have ht' : t'.val+1=(k::ks).length := by
        simp only [List.length_cons] at ht ⊢
        dsimp [t']
        omega
      have hh := ih (s.cross a i height (hc i (by simp)))
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i (k::ks) hn hc) t' ht'
      simpa only [rowFresh,dite_eq_right ht0,t',IntervalState.crossRequests] using hh

theorem row_outgoing (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (t : Fin rs.length) (ht : t.val +1=rs.length) :
    (s.crossRequests a height rs hn hc).adj
      ((s.crossRequests a height rs hn hc).positioned.registry.xors.embed a 7)
      (rowFresh s a height rs hn hc t (rowPort true)) := by
  induction rs generalizing s with
  | nil => exact Fin.elim0 t
  | cons i is ih =>
    cases is with
    | nil =>
      have ht0 : t.val=0 := by simp only [List.length_cons,List.length_nil] at ht; omega
      simp only [rowFresh,dite_eq_left ht0,rowLift,IntervalState.crossRequests]
      rw [Horizontal.latest_active]
      change Adj 4 (x 0 7) (row 0 true)
      decide +kernel
    | cons k ks =>
      have ht0 : t.val≠0 := by simp only [List.length_cons] at ht; omega
      let t' : Fin (k::ks).length := ⟨t.val-1,by
        simp only [List.length_cons] at ht ⊢
        omega⟩
      have ht' : t'.val+1=(k::ks).length := by
        simp only [List.length_cons] at ht ⊢
        dsimp [t']
        omega
      have hh := ih (s.cross a i height (hc i (by simp)))
        (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i (k::ks) hn hc) t' ht'
      simpa only [rowFresh,dite_eq_right ht0,t',IntervalState.crossRequests] using hh

def lastIndex (height : Nat → Nat) (n j : Nat) (a : Fin n) (i : Nat)
    (hi : (requests height (j +a.val)).getLast? =some i) : Fin (moveCount height n j) :=
  ⟨(trace height n j).idxOf (i,j+a.val),by
    rw [←trace_length]
    apply List.idxOf_lt_length_of_mem
    have hm := (mem_requests height i (j+a.val)).mp (List.mem_of_getLast? hi)
    exact (mem_trace height n j (i,j+a.val)).mpr
      ⟨hm.1,hm.2,by omega,by have := a.isLt; omega⟩⟩

theorem lastIndex_head (height : Nat → Nat) (n j i : Nat)
    (hi : (requests height j).getLast? =some i) :
    (trace height (n+1) j).idxOf (i,j)+1=(requests height j).length := by
  have hm := List.mem_of_getLast? hi
  have hmap : (i,j)∈(requests height j).map (fun k => (k,j)) :=
    List.mem_map.mpr ⟨i,hm,rfl⟩
  rw [trace,List.idxOf_append,ite_eq_left hmap]
  obtain ⟨ks,hks⟩ := List.getLast?_eq_some_iff.mp hi
  have hn := requests_nodup height j
  rw [hks] at hn
  have hni : i∉ks := by
    have hd := (List.nodup_append.mp hn).2.2
    intro hm
    exact hd i hm i (by simp) rfl
  have hni' : (i,j)∉ks.map (fun k => (k,j)) := by
    intro h
    obtain ⟨k,hk,he⟩ := List.mem_map.mp h
    have hki : k=i := congrArg Prod.fst he
    exact hni (hki ▸ hk)
  rw [hks,List.map_append,List.idxOf_append,ite_eq_right hni']
  simp

theorem run_incoming (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (i : Nat) (hi : (requests height (j+a.val)).getLast?=some i),
      (runState height hinj hpos n j s h).adj
        (runFresh height hinj hpos n j s h (lastIndex height n j a i hi) (rowPort false))
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a 4)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a i hi
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have hi' : (requests height j).getLast?=some i := by simpa using hi
      have ht : (lastIndex height (n+1) j 0 i hi).val+1=(requests height j).length :=
        lastIndex_head height n j i hi'
      have hlt : (lastIndex height (n+1) j 0 i hi).val<(requests height j).length := by omega
      simp only [runFresh,dite_eq_left hlt,runLift,nextLift,rowLift_current_xor,runState]
      apply (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (TrueEdges.retire_safe _ _ _ _ false _
          (RetainedEdges.rowFresh_safe s 0 (height j) (requests height j) (requests_nodup height j)
            h.requests_covered _ false (rowPort false) (RetainedEdges.input_direction 0)))
        (RetiredSideEdges.retire_safe _ _ _ _ true 4 (by decide +kernel))).mpr
      exact row_incoming s 0 (height j) (requests height j) (requests_nodup height j)
        h.requests_covered _ ht
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hb : b.succ=a := by apply Fin.ext; dsimp [b]; omega
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have hi' : (requests height (j+1+b.val)).getLast?=some i := by simpa only [hj] using hi
      have ht : (lastIndex height (n+1) j a i hi).val=
          (lastIndex height n (j+1) b i hi').val+(requests height j).length := by
        dsimp only [lastIndex]
        rw [hj]
        exact FalseEdges.firstIndex_succ height n j i a.val (by omega)
      have hlt : ¬(lastIndex height (n+1) j a i hi).val<(requests height j).length := by omega
      have he : (⟨(lastIndex height (n+1) j a i hi).val-(requests height j).length,
          by have := (lastIndex height (n+1) j a i hi).isLt
             simp only [moveCount] at this
             omega⟩ : Fin (moveCount height n (j+1)))=lastIndex height n (j+1) b i hi' := by
        apply Fin.ext
        dsimp
        omega
      simp only [runFresh,dite_eq_right hlt,runLift,nextLift,
        FalseEdges.rowLift_other_xor s 0 a (by intro he; apply ha; exact congrArg Fin.val he),runState]
      rw [he]
      have hh := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b i hi'
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj _
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed b.succ 4)) at hh
      simpa only [hb,crossed] using hh

theorem run_outgoing (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (i : Nat) (hi : (requests height (j+a.val)).getLast?=some i),
      (runState height hinj hpos n j s h).adj
        (runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a 7))
        (runFresh height hinj hpos n j s h (lastIndex height n j a i hi) (rowPort true)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a i hi
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have hi' : (requests height j).getLast?=some i := by simpa using hi
      have ht : (lastIndex height (n+1) j 0 i hi).val+1=(requests height j).length :=
        lastIndex_head height n j i hi'
      have hlt : (lastIndex height (n+1) j 0 i hi).val<(requests height j).length := by omega
      simp only [runFresh,dite_eq_left hlt,runLift,nextLift,rowLift_current_xor,runState]
      apply (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (RetiredSideEdges.retire_safe _ _ _ _ false 7 (by decide +kernel))
        (TrueEdges.retire_safe _ _ _ _ true _
          (RetainedEdges.rowFresh_safe s 0 (height j) (requests height j) (requests_nodup height j)
            h.requests_covered _ true (rowPort true) (RetainedEdges.output_direction 0)))).mpr
      exact row_outgoing s 0 (height j) (requests height j) (requests_nodup height j)
        h.requests_covered _ ht
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hb : b.succ=a := by apply Fin.ext; dsimp [b]; omega
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have hi' : (requests height (j+1+b.val)).getLast?=some i := by simpa only [hj] using hi
      have ht : (lastIndex height (n+1) j a i hi).val=
          (lastIndex height n (j+1) b i hi').val+(requests height j).length := by
        dsimp only [lastIndex]
        rw [hj]
        exact FalseEdges.firstIndex_succ height n j i a.val (by omega)
      have hlt : ¬(lastIndex height (n+1) j a i hi).val<(requests height j).length := by omega
      have he : (⟨(lastIndex height (n+1) j a i hi).val-(requests height j).length,
          by have := (lastIndex height (n+1) j a i hi).isLt
             simp only [moveCount] at this
             omega⟩ : Fin (moveCount height n (j+1)))=lastIndex height n (j+1) b i hi' := by
        apply Fin.ext
        dsimp
        omega
      simp only [runFresh,dite_eq_right hlt,runLift,nextLift,
        FalseEdges.rowLift_other_xor s 0 a (by intro he; apply ha; exact congrArg Fin.val he),runState]
      rw [he]
      have hh := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h) b i hi'
      change (runState height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)).adj
        (runLift height hinj hpos n (j+1) (next s height j h)
          (next_ready s height hinj hpos j h)
          ((crossed s height j h).positioned.registry.xors.embed b.succ 7)) _ at hh
      simpa only [hb,crossed] using hh

open PlanarSatAssembly
variable {m : Nat}

theorem permutation_incoming (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (i j : Fin (3 *m)) (hi : SatCrossingRetirement.Catalogue.lastRequest? p j =some i) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.fresh φ p
        ⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩ (rowPort false))
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm j) 4)) := by
  have hh := SatCrossingRetirement.Catalogue.lastRequest_val p j
  rw [hi] at hh
  have hh' : (requests (permutationHeight p) (0+j.val)).getLast?=some i.val := by
    simpa using hh.symm
  have he : lastIndex (permutationHeight p) (3*m) 0 j i.val hh'=
      (PermutationWirePlacement.crossingEquiv p).symm
        ⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩ := by
    apply Fin.ext
    rw [PermutationWirePlacement.crossingEquiv_symm_val]
    simp only [lastIndex,Nat.zero_add]
  have hr := run_incoming (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j i.val hh'
  rw [he] at hr
  exact hr

theorem permutation_outgoing (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (i j : Fin (3 *m)) (hi : SatCrossingRetirement.Catalogue.lastRequest? p j =some i) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p (PlanarSatAssembly.xor ((SatWireLayout.variableRank φ).symm j) 7))
      (PermutationWirePlacement.fresh φ p
        ⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩ (rowPort true)) := by
  have hh := SatCrossingRetirement.Catalogue.lastRequest_val p j
  rw [hi] at hh
  have hh' : (requests (permutationHeight p) (0+j.val)).getLast?=some i.val := by
    simpa using hh.symm
  have he : lastIndex (permutationHeight p) (3*m) 0 j i.val hh'=
      (PermutationWirePlacement.crossingEquiv p).symm
        ⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩ := by
    apply Fin.ext
    rw [PermutationWirePlacement.crossingEquiv_symm_val]
    simp only [lastIndex,Nat.zero_add]
  have hr := run_outgoing (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j i.val hh'
  rw [he] at hr
  exact hr

theorem placement_incoming (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (i j : Fin (3 *m)) (hi : SatCrossingRetirement.Catalogue.lastRequest? p j =some i) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.vertex φ p
        (.inr (⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩,rowPort false)))
      (PermutationWirePlacement.vertex φ p (.inl (j,4))) := by
  rw [PermutationWirePlacement.vertex_fresh,PermutationWirePlacement.vertex_original]
  exact permutation_incoming φ p i j hi

theorem placement_outgoing (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (i j : Fin (3 *m)) (hi : SatCrossingRetirement.Catalogue.lastRequest? p j =some i) :
    (PermutationGraph.graph φ p).adj
      (PermutationWirePlacement.vertex φ p (.inl (j,7)))
      (PermutationWirePlacement.vertex φ p
        (.inr (⟨(i,j),(SatCrossingRetirement.Catalogue.lastRequest_sound p i j hi).1⟩,rowPort true))) := by
  rw [PermutationWirePlacement.vertex_original,PermutationWirePlacement.vertex_fresh]
  exact permutation_outgoing φ p i j hi

end GridHardness.CorrectedSatInterval.LastLinks
