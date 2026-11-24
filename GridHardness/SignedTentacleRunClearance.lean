/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleRunChain

/-!
# Signed Tentacle Run Clearance

Clearance of ideal centerlines implies clearance of the compiled
width-two strips. A six-step margin leaves at least two steps between
strip vertices, because each strip lies within distance two of its ideal
segment. This discharges the global premise of the run-chain compiler.
-/

@[expose] public section

namespace GridHardness.SignedTentacle.RunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def segmentStrip (a : Segment) : Finset Point := strip a.1.frame (a.1.length a.2)

/-- A six-step separation between the two finite ideal segments. -/
def SegmentFar (a b : Segment) : Prop :=
  ∀ k : Int, 0 ≤ k → k ≤ a.2 → ∀ l : Int, 0 ≤ l → l ≤ b.2 →
    6 ≤ IntegerGrid.manhattan (a.1.point k) (b.1.point l)

theorem segment_strip_distance (a b : Segment) (h : SegmentFar a b)
    (p q : Point) (hp : p ∈ segmentStrip a) (hq : q ∈ segmentStrip b) :
    2 ≤ IntegerGrid.manhattan p q := by
  obtain ⟨k, hk0, hka, hkp⟩ := a.1.strip_distance a.2 p hp
  obtain ⟨l, hl0, hlb, hlq⟩ := b.1.strip_distance b.2 q hq
  have hd := h k hk0 hka l hl0 hlb
  have ht1 := IntegerGrid.manhattan_triangle (a.1.point k) p (b.1.point l)
  have ht2 := IntegerGrid.manhattan_triangle p q (b.1.point l)
  rw [IntegerGrid.manhattan_comm (a.1.point k) p] at ht1
  omega

theorem segment_strips_apart (a b : Segment) (h : SegmentFar a b) :
    ClusterStar.Apart (segmentStrip a) (segmentStrip b) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := segment_strip_distance a b h p p hp hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := segment_strip_distance a b h p q hp hq
    change IntegerGrid.manhattan p q = 1 at ha
    omega

/-- The geometric premise is indexed by actual positions in the generated
run list. Only nonconsecutive segments must be six steps apart. -/
def IndexedClearance (ss : List Segment) : Prop :=
  ∀ i j (hi : i < ss.length) (hj : j < ss.length), i + 1 < j →
    SegmentFar (ss[i]'hi) (ss[j]'hj)

/-- Recursive view of the same nonconsecutive separation requirement. -/
def Nonconsecutive : List Segment → Prop
  | [] => True
  | a::ss => (∀ b ∈ ss.tail, SegmentFar a b) ∧ Nonconsecutive ss

theorem indexedClearance_tail (a : Segment) (ss : List Segment)
    (h : IndexedClearance (a::ss)) : IndexedClearance ss := by
  intro i j hi hj hij
  have hh := h (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
  simpa only [List.getElem_cons_succ] using hh

theorem nonconsecutive_of_indexed (ss : List Segment) (h : IndexedClearance ss) :
    Nonconsecutive ss := by
  induction ss with
  | nil => trivial
  | cons a ss ih =>
    refine ⟨?_, ih (indexedClearance_tail a ss h)⟩
    intro b hb
    cases ss with
    | nil => simp at hb
    | cons c ss =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hh := h 0 (i + 2) (by simp) (by simp at hi ⊢; omega) (by omega)
      simpa only [List.getElem_cons_succ, List.getElem_cons_zero, List.tail_cons] using hh

theorem runs_self_tail (s : RunState) (length : Nat) (rs : List Request) :
    runs s length rs = (s, length)::(runs s length rs).tail := by
  cases rs with
  | nil => rfl
  | cons r rs => cases r; rfl

theorem execute_mem (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) (p : Point) :
    p ∈ (execute d s length rs).points ↔
      p ∈ d.points ∨ ∃ a ∈ (runs s length rs).tail, p ∈ segmentStrip a := by
  induction rs generalizing d s length with
  | nil => simp [execute, runs]
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    rw [execute, ih]
    change (p ∈ d.points ∪ segmentStrip (s.advance length down, n) ∨
      ∃ a ∈ (runs (s.advance length down) n rs).tail, p ∈ segmentStrip a) ↔
      p ∈ d.points ∨ ∃ a ∈ runs (s.advance length down) n rs, p ∈ segmentStrip a
    conv_rhs => rw [runs_self_tail]
    simp only [Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    tauto

/-- Exact set membership for the generated drawing, without any validity
or separation assumption. -/
theorem compile_mem (s : RunState) (length : Nat) (rs : List Request) (p : Point) :
    p ∈ (compile s length rs).points ↔
      ∃ a ∈ runs s length rs, p ∈ segmentStrip a := by
  rw [compile, execute_mem]
  conv_rhs => rw [runs_self_tail]
  simp only [List.mem_cons, exists_eq_or_imp]
  rfl

/-- Every point of the compiled drawing remains within distance two of
one of the finite ideal segments. -/
theorem compile_centerline_distance (s : RunState) (length : Nat)
    (rs : List Request) (p : Point) (hp : p ∈ (compile s length rs).points) :
    ∃ a ∈ runs s length rs, ∃ k : Int, 0 ≤ k ∧ k ≤ a.2 ∧
      IntegerGrid.manhattan p (a.1.point k) ≤ 2 := by
  obtain ⟨a, ha, hpa⟩ := (compile_mem s length rs p).mp hp
  exact ⟨a, ha, a.1.strip_distance a.2 p hpa⟩

private theorem apart_of_covered (S : Finset Point) (history : List Segment) (b : Segment)
    (hc : ∀ p ∈ S, ∃ a ∈ history, p ∈ segmentStrip a)
    (hf : ∀ a ∈ history, SegmentFar a b) : ClusterStar.Apart S (segmentStrip b) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hpb
    obtain ⟨a, ha, hpa⟩ := hc p hp
    exact Finset.disjoint_left.mp (segment_strips_apart a b (hf a ha)).1 hpa hpb
  · intro p hp q hq ha
    obtain ⟨a, ham, hpa⟩ := hc p hp
    exact (segment_strips_apart a b (hf a ham)).2 p hpa q hq ha

/-- A prefix bookkeeping lemma: the earlier strips remain clear of all
future segments, while indexed separation supplies the new obligation
when the current terminal strip becomes part of that prefix. -/
theorem prefixClearance_of_nonconsecutive (d : Drawing) (s : RunState)
    (length : Nat) (rs : List Request) (history : List Segment)
    (hf : d.lastFrame = s.frame) (hl : d.lastLength = s.length length)
    (hp : ∀ p ∈ d.prefixPoints, ∃ a ∈ history, p ∈ segmentStrip a)
    (hc : ∀ a ∈ history, ∀ b ∈ (runs s length rs).tail, SegmentFar a b)
    (hn : Nonconsecutive (runs s length rs)) : PrefixClearance d s length rs := by
  induction rs generalizing d s length history with
  | nil => trivial
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    let t := s.advance length down
    have hhead : (t, n) ∈ runs t n rs := by
      rw [runs_self_tail]
      simp
    have hfar : ∀ a ∈ history, SegmentFar a (t, n) := by
      intro a ha
      exact hc a ha (t, n) hhead
    refine ⟨apart_of_covered d.prefixPoints history (t, n) hp hfar, ?_⟩
    apply ih (.attach d t.frame (t.length n)) t n (history ++ [(s, length)]) rfl rfl
    · intro p hpm
      change p ∈ d.points at hpm
      rw [d.points_prefix, Finset.mem_union] at hpm
      rcases hpm with hpm | hpm
      · obtain ⟨a, ha, hpa⟩ := hp p hpm
        exact ⟨a, by simp [ha], hpa⟩
      · refine ⟨(s, length), by simp, ?_⟩
        simpa only [segmentStrip, hf, hl] using hpm
    · intro a ha b hb
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · apply hc a ha b
        exact List.mem_of_mem_tail hb
      · exact hn.1 b hb
    · exact hn.2

/-- The global premise supplied to the compiler is a concrete
centerline-distance condition over the generated run indices. -/
theorem compile_prefixClearance (s : RunState) (length : Nat) (rs : List Request)
    (h : IndexedClearance (runs s length rs)) :
    PrefixClearance (.base s.frame (s.length length)) s length rs := by
  apply prefixClearance_of_nonconsecutive _ _ _ _ [] rfl rfl
  · intro p hp
    simp [Drawing.prefixPoints] at hp
  · simp
  · exact nonconsecutive_of_indexed _ h

theorem compile_valid_of_segment_distance (s : RunState) (length : Nat)
    (rs : List Request) (hl : 3 ≤ length) (hn : ∀ r ∈ rs, 3 ≤ r.2)
    (h : IndexedClearance (runs s length rs)) : (compile s length rs).Valid :=
  compile_valid s length rs hl hn (compile_prefixClearance s length rs h)

end GridHardness.SignedTentacle.RunChain
