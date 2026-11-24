/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryIntervalSelection
public import GridHardness.XorLineScheduleRun

/-!
# XOR Line Registry Interval Run

Execute requests against the changing, explicitly enumerated interval
registry. Each request performs an actual XOR-line replacement.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry

structure IntervalState (n : Nat) extends XorLineSchedule.FiniteGraph where
  BundleId : Type
  decEq : DecidableEq BundleId
  positioned : Positioned adj (Fin n) BundleId
  enum : List BundleId
  complete : ∀b, b∈enum

namespace IntervalState
variable {n : Nat}

instance (s : IntervalState n) : Finite s.Vertex := s.finite
instance (s : IntervalState n) : DecidableEq s.BundleId := s.decEq

def Covered (s : IntervalState n) (line height : Nat) : Prop :=
  ∃b, (s.positioned.segments b).Contains line height

/-- A bounded list search selects the unique actual bundle at a crossing. -/
def select (s : IntervalState n) (line height : Nat) (hc : s.Covered line height) :
    {b : s.BundleId // (s.positioned.segments b).Contains line height} :=
  match h : Intervals.lookup s.positioned.segments s.enum line height with
  | some b => ⟨b,Intervals.lookup_sound _ _ _ _ h⟩
  | none => False.elim (by
      obtain ⟨b,hb⟩ := Intervals.lookup_exists s.positioned.segments s.enum
        line height s.complete hc
      rw [h] at hb
      cases hb)

def cross (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) : IntervalState n where
  Vertex := s.positioned.registry.CrossVertex a (s.select line height hc).val
  finite := inferInstance
  adj := s.positioned.registry.crossAdj a (s.select line height hc).val
  BundleId := Registry.SplitIndex (s.select line height hc).val
  decEq := inferInstance
  positioned := s.positioned.cross a (s.select line height hc).val height
    (s.select line height hc).property.2
  enum := Intervals.splitEnum s.enum (s.select line height hc).val
  complete := Intervals.splitEnum_complete s.enum _ s.complete

theorem cross_correct (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) :
    PathCover.Hamiltonian s.adj ↔ PathCover.Hamiltonian (s.cross a line height hc).adj :=
  s.positioned.registry.cross_correct a _

theorem cross_vertex_count (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) :
    Nat.card (s.cross a line height hc).Vertex=Nat.card s.Vertex+40 :=
  s.positioned.registry.cross_vertex_count a (s.select line height hc).val

theorem cross_enum_length_le (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) :
    (s.cross a line height hc).enum.length≤s.enum.length+2 :=
  Intervals.splitEnum_length_le s.enum (s.select line height hc).val

theorem cross_coverage (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (i z : Nat) (hsep : i ≠line ∨ z ≠height) :
    (s.cross a line height hc).Covered i z ↔ s.Covered i z := by
  apply Intervals.coverage_cut_separate
  · exact (s.select line height hc).property.2
  · rcases hsep with hi | hz
    · exact Or.inl (by rw [(s.select line height hc).property.1]; exact hi)
    · exact Or.inr hz

theorem cross_line_bound (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (bound : Nat)
    (hb : ∀ b, (s.positioned.segments b).line <bound) :
    ∀b, ((s.cross a line height hc).positioned.segments b).line<bound := by
  intro b
  cases b with
  | inl b => exact hb b.val
  | inr t => cases t <;> exact hb (s.select line height hc).val

theorem cross_remaining_covered (s : IntervalState n) (a : Fin n) (height i : Nat)
    (is : List Nat) (hn : (i::is).Nodup)
    (hc : ∀ j∈i::is, s.Covered j height) :
    ∀j∈is, (s.cross a i height (hc i (by simp))).Covered j height := by
  intro j hj
  apply (s.cross_coverage a i height (hc i (by simp)) j height ?_).mpr (hc j (by simp [hj]))
  exact Or.inl (by intro he; subst j; exact (List.nodup_cons.mp hn).1 hj)

/-- Insert one horizontal line, crossing its requested old lines in list order.
No bundle label is supplied by the caller: every step finds it in the current
residual interval registry. -/
def crossRequests (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) : IntervalState n :=
  match requests with
  | [] => s
  | i::is =>
    crossRequests (s.cross a i height (hc i (by simp))) a height is
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)

theorem crossRequests_correct (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) :
    PathCover.Hamiltonian s.adj ↔
      PathCover.Hamiltonian (s.crossRequests a height requests hn hc).adj := by
  induction requests generalizing s with
  | nil => rfl
  | cons i is ih => exact (s.cross_correct a i height _).trans (ih _ _ _)

theorem crossRequests_vertex_count (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) :
    Nat.card (s.crossRequests a height requests hn hc).Vertex=
      Nat.card s.Vertex+40*requests.length := by
  induction requests generalizing s with
  | nil => simp [crossRequests]
  | cons i is ih =>
    change Nat.card ((s.cross a i height _).crossRequests a height is _ _).Vertex=_
    rw [ih,cross_vertex_count,List.length_cons]
    omega

theorem crossRequests_enum_length_le (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) :
    (s.crossRequests a height requests hn hc).enum.length≤
      s.enum.length+2*requests.length := by
  induction requests generalizing s with
  | nil => simp [crossRequests]
  | cons i is ih =>
    change ((s.cross a i height _).crossRequests a height is _ _).enum.length≤_
    have h := ih (s.cross a i height (hc i (by simp))) (List.nodup_cons.mp hn).2
      (s.cross_remaining_covered a height i is hn hc)
    have hc := s.cross_enum_length_le a i height (hc i (by simp))
    simp only [List.length_cons]
    omega

theorem crossRequests_coverage (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) (i z : Nat)
    (hsep : i ∉requests ∨ z ≠height) :
    (s.crossRequests a height requests hn hc).Covered i z ↔ s.Covered i z := by
  induction requests generalizing s with
  | nil => rfl
  | cons j js ih =>
    change ((s.cross a j height _).crossRequests a height js _ _).Covered i z↔_
    have hhead : i≠j ∨ z≠height := by
      rcases hsep with h | h
      · exact Or.inl (fun he => h (by simp [he]))
      · exact Or.inr h
    have htail : i∉js ∨ z≠height := by
      rcases hsep with h | h
      · exact Or.inl (fun hi => h (by simp [hi]))
      · exact Or.inr h
    exact (ih _ _ _ htail).trans (s.cross_coverage a j height _ i z hhead)

theorem crossRequests_line_bound (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j∈requests, s.Covered j height) (bound : Nat)
    (hb : ∀ b, (s.positioned.segments b).line <bound) :
    ∀b, ((s.crossRequests a height requests hn hc).positioned.segments b).line<bound := by
  induction requests generalizing s with
  | nil => exact hb
  | cons i is ih => exact ih _ _ _ (s.cross_line_bound a i height _ bound hb)

def retire (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) : IntervalState n where
  Vertex := s.Vertex
  finite := s.finite
  adj := s.adj
  BundleId := Option s.BundleId
  decEq := inferInstance
  positioned := s.positioned.retire line upper hfresh
  enum := none::s.enum.map some
  complete := by
    intro b
    cases b with
    | none => simp
    | some b => simp [s.complete b]

theorem retire_coverage (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) (i z : Nat) :
    (s.retire line upper hfresh).Covered i z ↔
      (i=line ∧ 0<z ∧ z<upper) ∨ s.Covered i z :=
  Intervals.coverage_extend s.positioned.segments line upper i z

theorem retire_enum_length (s : IntervalState (n +1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠line) :
    (s.retire line upper hfresh).enum.length=s.enum.length+1 := by
  simp [retire]

end IntervalState
end GridHardness.XorLineRegistry
