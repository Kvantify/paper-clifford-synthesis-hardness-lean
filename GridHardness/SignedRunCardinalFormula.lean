/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCode
public import GridHardness.SignedTentacleDrawingFrom

/-!
# Signed Run Cardinal Formula

A nonrecursive formula for the states of a cardinal strip chain.
After the first strip, the transverse sign is the preceding longitudinal
sign and the phase depends only on the longitudinal sign two runs back.
Thus the executable compiler needs bounded prefix sums and two indexed
lookups, rather than a general stateful fold.
-/

@[expose] public section

namespace GridHardness.SignedRunCardinalFormula
open CliffordSynthesis OrthogonalTentacle SignedTentacle SignedRunCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev Run := LatticeRouteRuns.Run

def negative (d : Fin 4) : Bool := decide (2 ≤ d.val)

/-- A lane-zero state reconstructed from its ideal start and two signs. -/
def regular (p : Point) (d : Fin 4) (previous older : Bool) : RunState where
  frame := ⟨decide (d.val % 2 = 0), negative d, previous,
    (frameAlong p d).map (-((bit (negative d ^^ older)).val : Int), 0)⟩
  phase := bit (negative d ^^ older)
  lane := 0

@[simp] theorem regular_direction (p : Point) (d : Fin 4) (a b : Bool) :
    (regular p d a b).frame.axisDirection = d := by
  fin_cases d <;> rfl

@[simp] theorem regular_start (p : Point) (d : Fin 4) (a b : Bool) :
    (regular p d a b).point 0 = p := by
  fin_cases d <;> cases a <;> cases b <;>
    simp [regular, negative, bit, RunState.point, runPoint, frameAlong,
      Frame.map, place, sign]

/-- The explicit formula agrees with the signed turn construction, including
the exceptional first transition from either initial lane. -/
theorem advance_regular (s : RunState) (n : Nat) (d : Fin 4)
    (hd : s.frame.axisDirection.val % 2 ≠ d.val % 2) :
    s.advance n (s.frame.chooseTurn d) =
      regular (s.point n) d s.frame.reverseX
        (s.frame.reverseY ^^ encodeBit s.lane) := by
  rcases s with ⟨⟨h,rx,ry,p⟩,phase,lane⟩
  cases h <;> cases rx <;> cases ry <;> fin_cases d <;>
    fin_cases phase <;> fin_cases lane <;>
    simp [Frame.axisDirection] at hd <;>
    simp [regular, negative, bit, encodeBit, RunState.advance, RunState.length,
      runLength, Frame.chooseTurn, nextFrame, turnFrame, Frame.comp,
      RunState.point, runPoint, frameAlong, Frame.map, place, sign, turnPhase] <;>
    omega

theorem regular_advance (p : Point) (d e : Fin 4) (a b : Bool) (n : Nat)
    (hd : d.val % 2 ≠ e.val % 2) :
    (regular p d a b).advance n ((regular p d a b).frame.chooseTurn e) =
      regular (LatticeRouteRuns.advance p d n) e (negative d) a := by
  rw [advance_regular _ _ _ (by simpa using hd), RunState.point_advance,
    regular_start, regular_direction]
  simp [regular, encodeBit]

/-- Total signed displacement of a cardinal run list. -/
def displacement (rs : List Run) : Point :=
  ((rs.map (fun r => (DirectedLocalLayout.ray r.1 r.2).1)).sum,
   (rs.map (fun r => (DirectedLocalLayout.ray r.1 r.2).2)).sum)

def translate (p : Point) (rs : List Run) : Point :=
  (p.1 + (displacement rs).1, p.2 + (displacement rs).2)

@[simp] theorem translate_nil (p : Point) : translate p [] = p := by
  simp [translate, displacement]

theorem translate_cons (p : Point) (d : Fin 4) (n : Nat) (rs : List Run) :
    translate p ((d,n)::rs) = translate (LatticeRouteRuns.advance p d n) rs := by
  simp [translate, displacement, LatticeRouteRuns.advance, Int.add_assoc]

/-- Reference local recurrence; the indexed formula below removes this fold
from the implementation of the polynomial program. -/
def regularRuns (p : Point) (older previous : Bool) : List Run → List RunChain.Segment
  | [] => []
  | (d,n)::rs => (regular p d previous older,n)::
      regularRuns (LatticeRouteRuns.advance p d n) previous (negative d) rs

def signHistory (older previous : Bool) (rs : List Run) : List Bool :=
  older::previous::rs.map (fun r => negative r.1)

def indexedRuns (p : Point) (older previous : Bool) (rs : List Run) : List RunChain.Segment :=
  rs.zipIdx.map (fun r =>
    (regular (translate p (rs.take r.2)) r.1.1
      ((signHistory older previous rs)[r.2+1]?.getD false)
      ((signHistory older previous rs)[r.2]?.getD false), r.1.2))

/-- Every indexed recipe gives the same ordered states as the local recurrence. -/
theorem indexedRuns_eq (p : Point) (older previous : Bool) (rs : List Run) :
    indexedRuns p older previous rs = regularRuns p older previous rs := by
  induction rs generalizing p older previous with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨d,n⟩
    simp only [indexedRuns, List.zipIdx_cons', List.map_cons, List.map_map,
      Function.comp_def, Prod.map, List.take_zero, translate_nil,
      signHistory, List.map_cons, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.take_succ_cons,
      translate_cons, regularRuns]
    congr 1
    exact ih (LatticeRouteRuns.advance p d n) previous (negative d)

/-- The generic signed chain starting from a regular state is the same
state list as the local cardinal recurrence. -/
theorem regularRuns_eq_runs (p : Point) (older previous : Bool) (d : Fin 4)
    (n : Nat) (rs : List Run)
    (hc : (d::rs.map Prod.fst).IsChain (fun a b => a.val % 2 ≠ b.val % 2)) :
    regularRuns p older previous ((d,n)::rs) =
      RunChain.runs (regular p d previous older) n
        (CardinalRunChain.requests (regular p d previous older) n rs) := by
  induction rs generalizing p older previous d n with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨e,m⟩
    have hd : d.val%2 ≠ e.val%2 := (List.isChain_cons_cons.mp hc).1
    simp only [regularRuns, CardinalRunChain.requests, RunChain.runs,
      regular_advance p d e previous older n hd]
    exact congrArg (List.cons (regular p d previous older,n))
      (ih _ _ _ _ _ hc.tail)

/-- The initial rectangle followed by the explicit indexed recipes is exactly
the state list used by `drawingFrom`. There are no geometric assumptions. -/
theorem initial_indexedRuns (s : RunState) (n : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun a b => a.val % 2 ≠ b.val % 2)) :
    (s,n)::indexedRuns (s.point n) (s.frame.reverseY ^^ encodeBit s.lane)
      s.frame.reverseX rs =
      RunChain.runs s n (CardinalRunChain.requests s n rs) := by
  rw [indexedRuns_eq]
  cases rs with
  | nil => rfl
  | cons r rs =>
    rcases r with ⟨d,m⟩
    have hd : s.frame.axisDirection.val%2 ≠ d.val%2 := (List.isChain_cons_cons.mp hc).1
    rw [CardinalRunChain.requests, RunChain.runs, advance_regular s n d hd]
    exact congrArg (List.cons (s,n)) (regularRuns_eq_runs _ _ _ _ _ _ hc.tail)

end GridHardness.SignedRunCardinalFormula
