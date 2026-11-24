/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalTrueEdges

/-!
# Corrected SAT Interval False Edges

The clause-side boundary of an occurrence wire is attached to the
first crossing in its row. Its two retained false ports subsequently
survive as core vertices, whereas the active true ports continue moving.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.FalseEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def falsePort (incoming : Bool) : Fin 8 := if incoming then 4 else 7

def retainedPort (incoming : Bool) : SatCrossingHorizontal.RetainedVertex :=
  ⟨if incoming then inputPort 4 (.inl false) else outputPort 4 (.inl false),
    by cases incoming <;> decide⟩

variable {n : Nat}

theorem retained_core (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (incoming : Bool) :
    CoreEdges.Core (s.cross a line height hc) (.inr (retainedPort incoming).val) := by
  constructor
  · intro b k
    by_cases hba : b=a
    · subst b
      rw [Horizontal.latest_active]
      intro he
      cases incoming
      all_goals
        have hh : (0 : Fin 5)=4 :=
          congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj he))
        exact (by decide : (0 : Fin 5)≠4) hh
    · change s.positioned.registry.crossXor a (s.select line height hc).val b k≠_
      rw [Registry.crossXor_other _ _ _ _ hba]
      intro he
      cases he
  · intro b q
    change endpoint (s.positioned.registry.splitBundle a (s.select line height hc).val
      BundleSegments.towardTrue b) q≠_
    cases b with
    | inl b =>
      change endpoint (s.positioned.registry.crossBundle a (s.select line height hc).val b.val) q≠_
      rw [Registry.crossBundle_other _ _ _ _ b.property]
      intro he
      cases he
    | inr side =>
      change endpoint (BundleSegments.side (s.positioned.registry.bundles (s.select line height hc).val)
        (s.positioned.registry.xors.embed a) _ _
        (BundleSegments.selected BundleSegments.towardTrue side)) q≠_
      rw [BundleSegments.side_endpoint_tag]
      cases he : BundleSegments.endpointTag BundleSegments.towardTrue (side,q) with
      | inl t => intro h; cases h
      | inr t =>
        cases incoming <;>
          simp [BundleSegments.tagVertex,retainedPort,inputPort,outputPort,x,row]

theorem cross_incoming (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.cross a line height hc).adj (crossLift s a line height hc v)
      (.inr (retainedPort true).val) ↔
      s.adj v (s.positioned.registry.xors.embed a 4) := by
  have hl := crossLift_survivor s a line height hc (CoreEdges.outside s a v hv)
  change crossLift s a line height hc v=_ at hl
  rw [hl]
  change (∃ p, Subdivision.Adj s.adj _ _ (.inl v)
    (sourceMarker (s.positioned.registry.xors.embed a) (Source.inputPort 4 p)) ∧
      inputPort 4 (.inl false)=inputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,he⟩
    have he' : p=.inl false := (inputPort_injective 4 he).symm
    subst p
    exact hp.1
  · intro he
    refine ⟨.inl false,⟨he,?_⟩,rfl⟩
    rintro ⟨i,hi,_⟩
    exact hv.bundle (s.select line height hc).val (i,false) hi.symm

theorem cross_outgoing (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.cross a line height hc).adj (.inr (retainedPort false).val)
      (crossLift s a line height hc v) ↔
      s.adj (s.positioned.registry.xors.embed a 7) v := by
  have hl := crossLift_survivor s a line height hc (CoreEdges.outside s a v hv)
  change crossLift s a line height hc v=_ at hl
  rw [hl]
  change (∃ p, Subdivision.Adj s.adj _ _
    (sourceMarker (s.positioned.registry.xors.embed a) (Source.outputPort 4 p)) (.inl v) ∧
      outputPort 4 (.inl false)=outputPort 4 p) ↔ _
  constructor
  · rintro ⟨p,hp,he⟩
    have he' : p=.inl false := (outputPort_injective 4 he).symm
    subst p
    exact hp.1
  · intro he
    refine ⟨.inl false,⟨he,?_⟩,rfl⟩
    rintro ⟨i,_,hi⟩
    exact hv.bundle (s.select line height hc).val (i,true) hi.symm

/-- Empty rows retain their original false port. Nonempty rows retain the
false port allocated by their first crossing, carried through the tail. -/
noncomputable def rowPort (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (incoming : Bool) : (s.crossRequests a height rs hn hc).Vertex :=
  match rs with
  | [] => s.positioned.registry.xors.embed a (falsePort incoming)
  | i::is => rowLift (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (.inr (retainedPort incoming).val)

theorem rowPort_fresh (s : IntervalState n) (a : Fin n) (height i : Nat)
    (is : List Nat) (hn : (i::is).Nodup) (hc : ∀ j ∈i::is, s.Covered j height)
    (incoming : Bool) :
    rowPort s a height (i::is) hn hc incoming=
      rowFresh s a height (i::is) hn hc ⟨0,by simp⟩ (retainedPort incoming) := by
  simp [rowPort,rowFresh]

theorem rowPort_core (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (hne : rs ≠[]) (incoming : Bool) :
    CoreEdges.Core (s.crossRequests a height rs hn hc) (rowPort s a height rs hn hc incoming) := by
  cases rs with
  | nil => exact False.elim (hne rfl)
  | cons i is =>
    exact CoreEdges.row_core _ _ _ _ _ _ _
      (retained_core s a i height (hc i (by simp)) incoming)

theorem row_incoming (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.crossRequests a height rs hn hc).adj (rowLift s a height rs hn hc v)
      (rowPort s a height rs hn hc true) ↔
      s.adj v (s.positioned.registry.xors.embed a 4) := by
  cases rs with
  | nil => rfl
  | cons i is =>
    exact (CoreEdges.row_adj _ _ _ _ _ _ _ _
      (CoreEdges.cross_core s a i height _ v hv)
      (retained_core s a i height _ true)).trans (cross_incoming s a i height _ v hv)

theorem row_outgoing (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.crossRequests a height rs hn hc).adj (rowPort s a height rs hn hc false)
      (rowLift s a height rs hn hc v) ↔
      s.adj (s.positioned.registry.xors.embed a 7) v := by
  cases rs with
  | nil => rfl
  | cons i is =>
    exact (CoreEdges.row_adj _ _ _ _ _ _ _ _
      (retained_core s a i height _ false)
      (CoreEdges.cross_core s a i height _ v hv)).trans (cross_outgoing s a i height _ v hv)

/-- A different live XOR is untouched by a crossing. The core endpoint
also prevents subdivision of the connecting arc. -/
theorem cross_other_incoming (s : IntervalState n) (a b : Fin n) (hba : b ≠a)
    (line height : Nat) (hc : s.Covered line height) (k : Fin 8)
    (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.cross a line height hc).adj (crossLift s a line height hc v)
      ((s.cross a line height hc).positioned.registry.xors.embed b k) ↔
      s.adj v (s.positioned.registry.xors.embed b k) := by
  have hl := crossLift_survivor s a line height hc (CoreEdges.outside s a v hv)
  change crossLift s a line height hc v=_ at hl
  rw [hl]
  change (s.cross a line height hc).adj _
    (s.positioned.registry.crossXor a (s.select line height hc).val b k) ↔ _
  rw [Registry.crossXor_other _ _ _ _ hba]
  change (s.adj v _ ∧ ¬∃ i,v=(s.positioned.registry.bundles (s.select line height hc).val).source i ∧
    s.positioned.registry.xors.embed b k=
      (s.positioned.registry.bundles (s.select line height hc).val).target i) ↔ _
  exact and_iff_left (by
    rintro ⟨i,hi,_⟩
    exact hv.bundle (s.select line height hc).val (i,false) hi.symm)

theorem cross_other_outgoing (s : IntervalState n) (a b : Fin n) (hba : b ≠a)
    (line height : Nat) (hc : s.Covered line height) (k : Fin 8)
    (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.cross a line height hc).adj
      ((s.cross a line height hc).positioned.registry.xors.embed b k)
      (crossLift s a line height hc v) ↔
      s.adj (s.positioned.registry.xors.embed b k) v := by
  have hl := crossLift_survivor s a line height hc (CoreEdges.outside s a v hv)
  change crossLift s a line height hc v=_ at hl
  rw [hl]
  change (s.cross a line height hc).adj
    (s.positioned.registry.crossXor a (s.select line height hc).val b k) _ ↔ _
  rw [Registry.crossXor_other _ _ _ _ hba]
  change (s.adj _ v ∧ ¬∃ i,
    s.positioned.registry.xors.embed b k=
      (s.positioned.registry.bundles (s.select line height hc).val).source i ∧
    v=(s.positioned.registry.bundles (s.select line height hc).val).target i) ↔ _
  exact and_iff_left (by
    rintro ⟨i,_,hi⟩
    exact hv.bundle (s.select line height hc).val (i,true) hi.symm)

theorem row_other_incoming (s : IntervalState n) (a b : Fin n) (hba : b ≠a)
    (height : Nat) (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (k : Fin 8) (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.crossRequests a height rs hn hc).adj (rowLift s a height rs hn hc v)
      ((s.crossRequests a height rs hn hc).positioned.registry.xors.embed b k) ↔
      s.adj v (s.positioned.registry.xors.embed b k) := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) _ _ _
      (CoreEdges.cross_core s a i height _ v hv)).trans
      (cross_other_incoming s a b hba i height _ k v hv)

theorem row_other_outgoing (s : IntervalState n) (a b : Fin n) (hba : b ≠a)
    (height : Nat) (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (k : Fin 8) (v : s.Vertex) (hv : CoreEdges.Core s v) :
    (s.crossRequests a height rs hn hc).adj
      ((s.crossRequests a height rs hn hc).positioned.registry.xors.embed b k)
      (rowLift s a height rs hn hc v) ↔
      s.adj (s.positioned.registry.xors.embed b k) v := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    exact (ih (s.cross a i height (hc i (by simp))) _ _ _
      (CoreEdges.cross_core s a i height _ v hv)).trans
      (cross_other_outgoing s a b hba i height _ k v hv)

theorem retire_false_safe (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (incoming : Bool) :
    TrueEdges.Safe (s.retire line upper hfresh) incoming
      (s.positioned.registry.xors.embed 0 (falsePort incoming)) := by
  constructor
  · intro a k he
    exact False.elim (s.positioned.registry.xors.distinct a.succ 0 (by simp) k _ he)
  · intro b i
    cases b with
    | none =>
      change endpoint (s.positioned.registry.xors.bundle 0) (i,incoming)≠_
      rw [family_endpoint]
      intro he
      have hk := (s.positioned.registry.xors.embed_injective 0) he
      have hn : ∀ (i : Fin 4) (b : Bool), xorEndpoint (i,b)≠falsePort b := by decide +kernel
      exact hn i incoming hk
    | some b => exact (s.positioned.registry.disjoint 0 b _ (i,incoming)).symm

noncomputable def nextPort (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (incoming : Bool) : (next s height j h).Vertex :=
  rowPort s 0 (height j) (requests height j) (requests_nodup height j)
    h.requests_covered incoming

theorem rowPort_eq_active_of_nil (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (he : rs =[]) (incoming : Bool) :
    rowPort s a height rs hn hc incoming=
      (s.crossRequests a height rs hn hc).positioned.registry.xors.embed a (falsePort incoming) := by
  subst rs
  rfl

theorem nextPort_safe (s : IntervalState (n +1)) (height : Nat → Nat) (j : Nat)
    (h : Ready s height j) (incoming : Bool) :
    TrueEdges.Safe (next s height j h) incoming (nextPort s height j h incoming) := by
  by_cases he : requests height j=[]
  · have hp : nextPort s height j h incoming=
        (crossed s height j h).positioned.registry.xors.embed 0 (falsePort incoming) := by
      exact rowPort_eq_active_of_nil s 0 (height j) _ _ _ he incoming
    rw [hp]
    exact retire_false_safe _ _ _ _ incoming
  · exact TrueEdges.core_safe _ incoming _
      (CoreEdges.retire_core _ _ _ _ _
        (rowPort_core s 0 (height j) (requests height j) (requests_nodup height j)
          h.requests_covered he incoming))

/-- Follow the false boundary of a designated live XOR through all later
rows. The recursion switches to ordinary vertex transport immediately
after that XOR's own row has executed. -/
noncomputable def runPort (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) : (n j : Nat) → (s : IntervalState n) →
    (h : Ready s height j) → Fin n → Bool →
      (runState height hinj hpos n j s h).Vertex
  | 0,_,_,_,a,_ => Fin.elim0 a
  | n+1,j,s,h,a,incoming =>
    if ha : a.val=0 then
      runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) (nextPort s height j h incoming)
    else
      runPort height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h)
        ⟨a.val-1,by have := a.isLt; omega⟩ incoming

theorem run_incoming (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (v : s.Vertex), CoreEdges.Core s v →
      ((runState height hinj hpos n j s h).adj (runLift height hinj hpos n j s h v)
        (runPort height hinj hpos n j s h a true) ↔
        s.adj v (s.positioned.registry.xors.embed a 4)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a v hv
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      simp only [runPort,Fin.val_zero,runLift,runState]
      exact (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (TrueEdges.core_safe _ false _ (CoreEdges.next_core s height j h v hv))
        (nextPort_safe s height j h true)).trans
        (row_incoming s 0 (height j) (requests height j) (requests_nodup height j)
          h.requests_covered v hv)
    · simp only [runPort,dite_eq_right ha,runLift,runState]
      have hb : (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ=a := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hh := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
        ⟨a.val-1,by have := a.isLt; omega⟩ (nextLift s height j h v)
        (CoreEdges.next_core s height j h v hv)
      apply hh.trans
      change (crossed s height j h).adj _ ((crossed s height j h).positioned.registry.xors.embed
        (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ 4) ↔ _
      rw [hb]
      exact row_other_incoming s 0 a (by intro he; apply ha; exact congrArg Fin.val he)
        (height j) (requests height j) (requests_nodup height j) h.requests_covered 4 v hv

theorem run_outgoing (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (v : s.Vertex), CoreEdges.Core s v →
      ((runState height hinj hpos n j s h).adj
        (runPort height hinj hpos n j s h a false) (runLift height hinj hpos n j s h v) ↔
        s.adj (s.positioned.registry.xors.embed a 7) v) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a v hv
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      simp only [runPort,Fin.val_zero,runLift,runState]
      exact (TrueEdges.run_adj height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h) _ _
        (nextPort_safe s height j h false)
        (TrueEdges.core_safe _ true _ (CoreEdges.next_core s height j h v hv))).trans
        (row_outgoing s 0 (height j) (requests height j) (requests_nodup height j)
          h.requests_covered v hv)
    · simp only [runPort,dite_eq_right ha,runLift,runState]
      have hb : (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ=a := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have hh := ih (j+1) (next s height j h) (next_ready s height hinj hpos j h)
        ⟨a.val-1,by have := a.isLt; omega⟩ (nextLift s height j h v)
        (CoreEdges.next_core s height j h v hv)
      apply hh.trans
      change (crossed s height j h).adj ((crossed s height j h).positioned.registry.xors.embed
        (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ 7) _ ↔ _
      rw [hb]
      exact row_other_outgoing s 0 a (by intro he; apply ha; exact congrArg Fin.val he)
        (height j) (requests height j) (requests_nodup height j) h.requests_covered 7 v hv

theorem rowLift_other_xor (s : IntervalState n) (a b : Fin n) (hba : b ≠a)
    (height : Nat) (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (k : Fin 8) :
    rowLift s a height rs hn hc (s.positioned.registry.xors.embed b k)=
      (s.crossRequests a height rs hn hc).positioned.registry.xors.embed b k := by
  induction rs generalizing s with
  | nil => rfl
  | cons i is ih =>
    change rowLift _ _ _ _ _ _
      (crossLift s a i height _ (s.positioned.registry.xors.embed b k))=_
    rw [crossLift_other_xor s a b hba i height]
    exact ih _ _ _

theorem runPort_empty (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (incoming : Bool), requests height (j+a.val)=[] →
      runPort height hinj hpos n j s h a incoming=
        runLift height hinj hpos n j s h (s.positioned.registry.xors.embed a (falsePort incoming)) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a incoming he
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have he' : requests height j=[] := by simpa using he
      simp only [runPort,Fin.val_zero,runLift]
      apply congrArg (runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h))
      exact (rowPort_eq_active_of_nil s 0 (height j) _ _ _ he' incoming).trans
        (rowLift_current_xor s 0 (height j) _ _ _ _).symm
    · simp only [runPort,dite_eq_right ha,runLift]
      have ha' : (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ=a := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      have he' : requests height (j+1+(a.val-1))=[] := by
        have hj : j+1+(a.val-1)=j+a.val := by omega
        simpa only [hj] using he
      rw [ih _ _ _ _ incoming he']
      apply congrArg (runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h))
      change (crossed s height j h).positioned.registry.xors.embed
        (⟨a.val-1,by have := a.isLt; omega⟩ : Fin n).succ _=_
      rw [ha']
      exact (rowLift_other_xor s 0 a (by intro he; apply ha; exact congrArg Fin.val he)
        (height j) (requests height j) (requests_nodup height j) h.requests_covered _).symm

def firstIndex (height : Nat → Nat) (n j : Nat) (a : Fin n) (i : Nat)
    (hi : (requests height (j +a.val)).head? =some i) : Fin (moveCount height n j) :=
  ⟨(trace height n j).idxOf (i,j+a.val),by
    rw [←trace_length]
    apply List.idxOf_lt_length_of_mem
    have hm := (mem_requests height i (j+a.val)).mp (List.mem_of_head? hi)
    exact (mem_trace height n j (i,j+a.val)).mpr
      ⟨hm.1,hm.2,by omega,by have := a.isLt; omega⟩⟩

theorem firstIndex_zero (height : Nat → Nat) (n j i : Nat)
    (hi : (requests height j).head? =some i) :
    (trace height (n+1) j).idxOf (i,j)=0 := by
  obtain ⟨is,hi⟩ := List.head?_eq_some_iff.mp hi
  simp [trace,hi]

theorem firstIndex_succ (height : Nat → Nat) (n j i a : Nat) (ha : 0 <a) :
    (trace height (n+1) j).idxOf (i,j+a)=
      (trace height n (j+1)).idxOf (i,j+a)+(requests height j).length := by
  rw [trace,List.idxOf_append,ite_eq_right]
  · simp
  · intro hm
    obtain ⟨k,_,he⟩ := List.mem_map.mp hm
    have hh := congrArg Prod.snd he
    dsimp at hh
    omega

theorem rowPort_head (s : IntervalState n) (a : Fin n) (height : Nat)
    (rs : List Nat) (hn : rs.Nodup) (hc : ∀ i ∈rs, s.Covered i height)
    (i : Nat) (hi : rs.head? =some i) (incoming : Bool) :
    rowPort s a height rs hn hc incoming=
      rowFresh s a height rs hn hc
        ⟨0,by cases rs <;> simp_all⟩ (retainedPort incoming) := by
  cases rs with
  | nil => simp at hi
  | cons k ks => simp [rowPort,rowFresh]

theorem runPort_fresh (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0<height i) (n : Nat) :
    ∀ (j : Nat) (s : IntervalState n) (h : Ready s height j) (a : Fin n)
      (i : Nat) (hi : (requests height (j+a.val)).head?=some i) (incoming : Bool),
      runPort height hinj hpos n j s h a incoming=
        runFresh height hinj hpos n j s h (firstIndex height n j a i hi) (retainedPort incoming) := by
  induction n with
  | zero => intro j s h a; exact Fin.elim0 a
  | succ n ih =>
    intro j s h a i hi incoming
    by_cases ha : a.val=0
    · have ha' : a=0 := Fin.ext ha
      subst a
      have hi' : (requests height j).head?=some i := by simpa using hi
      have ht : (firstIndex height (n+1) j 0 i hi).val=0 :=
        firstIndex_zero height n j i hi'
      have hn : 0<(requests height j).length := by
        obtain ⟨is,he⟩ := List.head?_eq_some_iff.mp hi'
        simp [he]
      simp only [runPort,Fin.val_zero,runFresh,ht,show 0<(requests height j).length from hn,
        ↓reduceDIte]
      exact congrArg (runLift height hinj hpos n (j+1) (next s height j h)
        (next_ready s height hinj hpos j h))
        (rowPort_head s 0 (height j) _ _ _ i hi' incoming)
    · let b : Fin n := ⟨a.val-1,by have := a.isLt; omega⟩
      have hj : j+1+b.val=j+a.val := by dsimp [b]; omega
      have hi' : (requests height (j+1+b.val)).head?=some i := by simpa only [hj] using hi
      have ht : (firstIndex height (n+1) j a i hi).val=
          (firstIndex height n (j+1) b i hi').val+(requests height j).length := by
        dsimp only [firstIndex]
        rw [hj]
        exact firstIndex_succ height n j i a.val (by omega)
      have hn : ¬(firstIndex height (n+1) j a i hi).val<(requests height j).length := by omega
      simp only [runPort,dite_eq_right ha,runFresh,dite_eq_right hn]
      have he : (⟨(firstIndex height (n+1) j a i hi).val-(requests height j).length,
          by have := (firstIndex height (n+1) j a i hi).isLt
             simp only [moveCount] at this
             omega⟩ : Fin (moveCount height n (j+1)))=firstIndex height n (j+1) b i hi' := by
        apply Fin.ext
        dsimp
        omega
      rw [he]
      exact ih _ _ _ b i hi' incoming

end GridHardness.CorrectedSatInterval.FalseEdges
