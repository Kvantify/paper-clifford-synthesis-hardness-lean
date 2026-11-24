/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleRunGeometry
public import GridHardness.SignedTentacleChain

/-!
# Signed Tentacle Run Chain

An executable chain of phase-corrected strips for a sequence of ideal
orthogonal runs. Consecutive ideal endpoints agree exactly. Local turn
geometry is automatic; global validity requires explicit clearance of
each new strip from the strips preceding its immediate neighbor.
-/

@[expose] public section

namespace GridHardness.SignedTentacle.RunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Request := Bool × Nat
abbrev Segment := RunState × Nat

/-- The generated strip states, including the initial run. -/
def runs (s : RunState) (length : Nat) : List Request → List Segment
  | [] => [(s, length)]
  | (down, n)::rs => (s, length)::runs (s.advance length down) n rs

/-- Final phase-corrected state and its ideal length. -/
def terminal (s : RunState) (length : Nat) : List Request → Segment
  | [] => (s, length)
  | (down, n)::rs => terminal (s.advance length down) n rs

/-- Append the requested strips in route order. -/
def execute (d : Drawing) (s : RunState) (length : Nat) : List Request → Drawing
  | [] => d
  | (down, n)::rs =>
      let t := s.advance length down
      execute (.attach d t.frame (t.length n)) t n rs

def compile (s : RunState) (length : Nat) (rs : List Request) : Drawing :=
  execute (.base s.frame (s.length length)) s length rs

def idealLength (length : Nat) (rs : List Request) : Nat :=
  length + (rs.map Prod.snd).sum

def stripCount : Drawing → Nat
  | .base _ _ => 1
  | .attach d _ _ => stripCount d + 1

theorem runs_length (s : RunState) (length : Nat) (rs : List Request) :
    (runs s length rs).length = rs.length + 1 := by
  induction rs generalizing s length with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨down, n⟩
    simp only [runs, List.length_cons, ih]

theorem runs_head (s : RunState) (length : Nat) (rs : List Request) :
    (runs s length rs).head? = some (s, length) := by
  cases rs with
  | nil => rfl
  | cons r rs => cases r; rfl

theorem runs_last (s : RunState) (length : Nat) (rs : List Request) :
    (runs s length rs).getLast? = some (terminal s length rs) := by
  induction rs generalizing s length with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨down, n⟩
    rw [runs, List.getLast?_cons]
    simp only [ih, Option.getD_some, terminal]

/-- The end of every ideal run is exactly the start of the next run. -/
theorem runs_join (s : RunState) (length : Nat) (rs : List Request) :
    (runs s length rs).IsChain (fun a b => a.1.point a.2 = b.1.point 0) := by
  induction rs generalizing s length with
  | nil => simp [runs]
  | cons r rs ih =>
    rcases r with ⟨down, n⟩
    rw [runs, List.isChain_cons]
    refine ⟨?_, ih _ _⟩
    intro t ht
    rw [runs_head] at ht
    have he : (s.advance length down, n) = t := by simpa using ht
    subst t
    exact (s.advance_start length down).symm

theorem execute_start (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) (r : Fin 2) :
    (execute d s length rs).start r = d.start r := by
  induction rs generalizing d s length with
  | nil => rfl
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    exact ih _ _ _

theorem compile_start (s : RunState) (length : Nat) (rs : List Request) (r : Fin 2) :
    (compile s length rs).start r = near s.frame r := execute_start _ _ _ _ _

/-- If the initial run has no prefix phase, its selected start lane is
the first ideal endpoint itself. -/
theorem compile_ideal_start (s : RunState) (length : Nat) (rs : List Request)
    (hs : s.phase = 0) :
    (compile s length rs).start s.lane = s.point 0 := by
  rw [compile_start]
  simp [RunState.point, runPoint, near, hs]

theorem execute_terminal (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) (hf : d.lastFrame = s.frame)
    (hl : d.lastLength = s.length length) :
    (execute d s length rs).lastFrame = (terminal s length rs).1.frame ∧
      (execute d s length rs).lastLength =
        (terminal s length rs).1.length (terminal s length rs).2 := by
  induction rs generalizing d s length with
  | nil => exact ⟨hf, hl⟩
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    exact ih _ _ _ rfl rfl

theorem compile_terminal (s : RunState) (length : Nat) (rs : List Request) :
    (compile s length rs).lastFrame = (terminal s length rs).1.frame ∧
      (compile s length rs).lastLength =
        (terminal s length rs).1.length (terminal s length rs).2 :=
  execute_terminal _ _ _ _ rfl rfl

/-- The selected final terminal vertex is exactly the final ideal
endpoint, regardless of the accumulated sequence of turns. -/
theorem compile_ideal_tip (s : RunState) (length : Nat) (rs : List Request) :
    (compile s length rs).tip (terminal s length rs).1.lane =
      (terminal s length rs).1.point (terminal s length rs).2 := by
  rw [Drawing.tip_last, (compile_terminal s length rs).1,
    (compile_terminal s length rs).2]
  simp [RunState.point, RunState.length, runPoint, runLength, far]

theorem execute_stripCount (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) : stripCount (execute d s length rs) = stripCount d + rs.length := by
  induction rs generalizing d s length with
  | nil => simp [execute]
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    simp only [execute, ih, stripCount, List.length_cons]
    omega

theorem compile_stripCount (s : RunState) (length : Nat) (rs : List Request) :
    stripCount (compile s length rs) = rs.length + 1 := by
  rw [compile, execute_stripCount, stripCount]
  omega

theorem execute_halfSize_le (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) :
    (execute d s length rs).halfSize ≤ d.halfSize + (rs.map Prod.snd).sum + rs.length := by
  induction rs generalizing d s length with
  | nil => simp [execute]
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    have hi := ih (.attach d (s.advance length down).frame
      ((s.advance length down).length n)) (s.advance length down) n
    have hb := (runLength_bounds (s.advance length down).phase n).2
    simp only [execute, Drawing.halfSize, List.map_cons, List.sum_cons,
      List.length_cons] at hi ⊢
    change (s.advance length down).length n ≤ n + 1 at hb
    omega

/-- At most one phase unit per run is added to the ideal total length. -/
theorem compile_halfSize_le (s : RunState) (length : Nat) (rs : List Request) :
    (compile s length rs).halfSize ≤ 1 + idealLength length rs + (rs.length + 1) := by
  have h := execute_halfSize_le (.base s.frame (s.length length)) s length rs
  have hb := (runLength_bounds s.phase length).2
  change s.length length ≤ length + 1 at hb
  simp only [Drawing.halfSize] at h
  simpa only [compile, Drawing.halfSize, idealLength] using (by omega :
    (execute (.base s.frame (s.length length)) s length rs).halfSize ≤
      1 + (length + (rs.map Prod.snd).sum) + (rs.length + 1))

/-- The remaining geometric checks are exactly nonconsecutive strip
clearance. Adjacent strips require no separately supplied certificate. -/
def PrefixClearance (d : Drawing) (s : RunState) (length : Nat) : List Request → Prop
  | [] => True
  | (down, n)::rs =>
      let t := s.advance length down
      ClusterStar.Apart d.prefixPoints (strip t.frame (t.length n)) ∧
        PrefixClearance (.attach d t.frame (t.length n)) t n rs

instance (d : Drawing) (s : RunState) (length : Nat) (rs : List Request) :
    Decidable (PrefixClearance d s length rs) := by
  induction rs generalizing d s length with
  | nil => exact inferInstanceAs (Decidable True)
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    change Decidable (ClusterStar.Apart d.prefixPoints
      (strip (s.advance length down).frame ((s.advance length down).length n)) ∧
      PrefixClearance (.attach d (s.advance length down).frame
        ((s.advance length down).length n)) (s.advance length down) n rs)
    letI := ih (.attach d (s.advance length down).frame
      ((s.advance length down).length n)) (s.advance length down) n
    infer_instance

theorem execute_valid (d : Drawing) (s : RunState) (length : Nat) (rs : List Request)
    (hd : d.Valid) (hf : d.lastFrame = s.frame) (hl : d.lastLength = s.length length)
    (hn : ∀ request ∈ rs, 3 ≤ request.2) (hc : PrefixClearance d s length rs) :
    (execute d s length rs).Valid := by
  induction rs generalizing d s length with
  | nil => exact hd
  | cons request rs ih =>
    rcases request with ⟨down, n⟩
    have hn' : 3 ≤ n := hn (down, n) (by simp)
    have hc' := hc.1
    have hlen := runLength_three (s.advance length down).phase n hn'
    have hturn := d.turn_valid hd down ((s.advance length down).length n) hlen
    rw [hf, hl] at hturn
    have hv : (Drawing.attach d (s.advance length down).frame
        ((s.advance length down).length n)).Valid := by
      simpa only [Drawing.turn, hf, hl, RunState.advance] using hturn hc'
    exact ih _ _ _ hv rfl rfl (fun r hr => hn r (by simp [hr])) hc.2

/-- A full validity theorem for the generated drawing. All local turns
and phase corrections are discharged; only explicit finite clearance
checks against nonconsecutive strips remain as geometric hypotheses. -/
theorem compile_valid (s : RunState) (length : Nat) (rs : List Request)
    (hl : 3 ≤ length) (hn : ∀ request ∈ rs, 3 ≤ request.2)
    (hc : PrefixClearance (.base s.frame (s.length length)) s length rs) :
    (compile s length rs).Valid :=
  execute_valid _ _ _ _ (runLength_three s.phase length hl) rfl rfl hn hc

end GridHardness.SignedTentacle.RunChain
