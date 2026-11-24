/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleCardinalFrames
public import GridHardness.SignedTentacleRunClearance
public import GridHardness.LatticeRouteRunsSubdivision

/-!
# Signed Tentacle Cardinal Runs

Compile cardinal straight runs into signed strip-chain requests.
The turn signs are calculated from the evolving frame. The generated
ideal route agrees point for point with the input cardinal-run expansion.
-/

@[expose] public section

namespace GridHardness.SignedTentacle.CardinalRunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Run := LatticeRouteRuns.Run

/-- Convert the remaining cardinal runs to relative signed turns while
carrying the exact frame and longitudinal phase. -/
def requests (s : RunState) (length : Nat) : List Run → List RunChain.Request
  | [] => []
  | (d, n)::rs =>
      let down := s.frame.chooseTurn d
      let t := s.advance length down
      (down, n)::requests t n rs

/-- Read the ideal finite segments represented by a signed request list.
Shared endpoints occur exactly once in this ordered point list. -/
def idealRoute (s : RunState) (length : Nat) : List RunChain.Request → List Point
  | [] => (List.range length).map (fun k : Nat => s.point k) ++ [s.point length]
  | (down, n)::rs => (List.range length).map (fun k : Nat => s.point k) ++
      idealRoute (s.advance length down) n rs

theorem requests_lengths (s : RunState) (length : Nat) (rs : List Run) :
    (requests s length rs).map Prod.snd = rs.map Prod.snd := by
  induction rs generalizing s length with
  | nil => rfl
  | cons r rs ih => cases r; simp only [requests, List.map_cons, ih]

theorem requests_length (s : RunState) (length : Nat) (rs : List Run) :
    (requests s length rs).length = rs.length := by
  have h := congrArg List.length (requests_lengths s length rs)
  simpa only [List.length_map] using h

theorem requests_lower (s : RunState) (length : Nat) (rs : List Run) (bound : Nat)
    (h : ∀ r ∈ rs, bound ≤ r.2) :
    ∀ r ∈ requests s length rs, bound ≤ r.2 := by
  intro r hr
  have hm : r.2 ∈ (requests s length rs).map Prod.snd := List.mem_map.mpr ⟨r, hr, rfl⟩
  rw [requests_lengths] at hm
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
  simpa only [he] using h a ha

theorem idealRoute_last (s : RunState) (length : Nat) (rs : List RunChain.Request) :
    (idealRoute s length rs).getLast? =
      some ((RunChain.terminal s length rs).1.point (RunChain.terminal s length rs).2) := by
  induction rs generalizing s length with
  | nil => simp [idealRoute, RunChain.terminal]
  | cons r rs ih =>
    rcases r with ⟨down, n⟩
    simp only [idealRoute, List.getLast?_append, ih, RunChain.terminal]
    rfl

/-- The signed constructor produces exactly the input sequence of ideal
points. Only perpendicularity is needed; zero lengths are also allowed
for this semantic identity. Positive length is required later for validity. -/
theorem idealRoute_requests (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    idealRoute s length (requests s length rs) =
      LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection, length)::rs) := by
  induction rs generalizing s length with
  | nil =>
    simp only [requests, idealRoute, LatticeRouteRuns.expandRuns,
      LatticeRouteRuns.walkInit_replicate, RunState.point_advance]
  | cons r rs ih =>
    rcases r with ⟨d, n⟩
    have hd : s.frame.axisDirection.val % 2 ≠ d.val % 2 := by
      have h := hc
      simp only [List.map_cons, List.isChain_cons_cons] at h
      exact h.1
    let t := s.advance length (s.frame.chooseTurn d)
    have ht : t.frame.axisDirection = d := s.advance_direction length d hd
    have hc' : (t.frame.axisDirection::rs.map Prod.fst).IsChain
        (fun d e => d.val % 2 ≠ e.val % 2) := by
      rw [ht]
      exact hc.tail
    change (List.range length).map (fun k : Nat => s.point k) ++
      idealRoute t n (requests t n rs) = _
    rw [ih t n hc', ht]
    change (List.range length).map (fun k : Nat => s.point k) ++
      LatticeRouteRuns.expandRuns ((s.advance length (s.frame.chooseTurn d)).point 0)
        ((d, n)::rs) = _
    rw [RunState.advance_start, RunState.point_advance]
    simp only [LatticeRouteRuns.expandRuns, LatticeRouteRuns.walkInit_replicate,
      RunState.point_advance]

/-- A concrete strip chain beginning at `p` and following a nonempty
cardinal run list, with canonical initial lane zero. -/
def drawing (p : Point) (d : Fin 4) (length : Nat) (rs : List Run) : Drawing :=
  RunChain.compile (initialRunState p d) length (requests (initialRunState p d) length rs)

theorem drawing_ideal_route (p : Point) (d : Fin 4) (length : Nat) (rs : List Run)
    (hc : (d::rs.map Prod.fst).IsChain (fun d e => d.val % 2 ≠ e.val % 2)) :
    idealRoute (initialRunState p d) length (requests (initialRunState p d) length rs) =
      LatticeRouteRuns.expandRuns p ((d, length)::rs) := by
  have hd : (initialRunState p d).frame.axisDirection = d := frameAlong_direction p d
  have h := idealRoute_requests (initialRunState p d) length rs (by rw [hd]; exact hc)
  rwa [initialRunState_point_zero, hd] at h

theorem drawing_start (p : Point) (d : Fin 4) (length : Nat) (rs : List Run) :
    (drawing p d length rs).start 0 = p := by
  have h := RunChain.compile_ideal_start (initialRunState p d) length
    (requests (initialRunState p d) length rs) rfl
  change (RunChain.compile (initialRunState p d) length
    (requests (initialRunState p d) length rs)).start (initialRunState p d).lane = p
  exact h.trans (initialRunState_point_zero p d)

/-- The final selected terminal lane is the actual endpoint of the
expanded cardinal input route. -/
theorem drawing_tip (p : Point) (d : Fin 4) (length : Nat) (rs : List Run)
    (hc : (d::rs.map Prod.fst).IsChain (fun d e => d.val % 2 ≠ e.val % 2)) :
    (LatticeRouteRuns.expandRuns p ((d, length)::rs)).getLast? =
      some ((drawing p d length rs).tip
        (RunChain.terminal (initialRunState p d) length
          (requests (initialRunState p d) length rs)).1.lane) := by
  rw [← drawing_ideal_route p d length rs hc, idealRoute_last]
  rw [drawing, RunChain.compile_ideal_tip]

theorem drawing_stripCount (p : Point) (d : Fin 4) (length : Nat) (rs : List Run) :
    RunChain.stripCount (drawing p d length rs) = rs.length + 1 := by
  rw [drawing, RunChain.compile_stripCount, requests_length]

theorem drawing_halfSize_le (p : Point) (d : Fin 4) (length : Nat) (rs : List Run) :
    (drawing p d length rs).halfSize ≤
      1 + (length + (rs.map Prod.snd).sum) + (rs.length + 1) := by
  have h := RunChain.compile_halfSize_le (initialRunState p d) length
    (requests (initialRunState p d) length rs)
  simpa only [drawing, RunChain.idealLength, requests_length, requests_lengths] using h

theorem drawing_valid (p : Point) (d : Fin 4) (length : Nat) (rs : List Run)
    (hl : 3 ≤ length) (hn : ∀ r ∈ rs, 3 ≤ r.2)
    (hclear : RunChain.IndexedClearance (RunChain.runs (initialRunState p d) length
      (requests (initialRunState p d) length rs))) : (drawing p d length rs).Valid :=
  RunChain.compile_valid_of_segment_distance _ _ _ hl
    (requests_lower _ _ _ 3 hn) hclear

end GridHardness.SignedTentacle.CardinalRunChain
