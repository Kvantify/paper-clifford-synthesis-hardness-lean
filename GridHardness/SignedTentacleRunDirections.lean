/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleDrawingFrom

/-!
# Signed Tentacle Run Directions

The first and last directions of the computed cardinal run list, and
the corresponding axis of the final compiled strip.
-/

public section

namespace GridHardness.LatticeRouteRuns
open LatticeRouteDirections
set_option autoImplicit false

theorem compress_initial_direction (l : List Point) (hl : 2 ≤ l.length) :
    ((compress l).map Prod.fst).head? = some (tangent l false hl) := by
  rw [compress, compress_head]
  cases l with
  | nil => simp at hl
  | cons p l =>
    cases l with
    | nil => simp at hl
    | cons q l => rfl

theorem compress_terminal_direction (l : List Point) (hl : 2 ≤ l.length)
    (hc : l.IsChain UnitStep) :
    ((compress l).map Prod.fst).getLast? = some (opposite (tangent l true hl)) := by
  have h := compress_initial_direction l.reverse (by simpa using hl)
  rw [compress_route_reverse l hc] at h
  simp only [List.map_map, Function.comp_def, List.head?_map, List.head?_reverse] at h
  have ht : tangent l.reverse false (by simpa using hl) = tangent l true hl := rfl
  rw [ht] at h
  have he : Option.map opposite (((compress l).map Prod.fst).getLast?) =
      some (tangent l true hl) := by
    simpa only [List.getLast?_map, Option.map_map, Function.comp_def] using h
  have hh := congrArg (Option.map opposite) he
  simpa only [Option.map_map, Function.comp_def, opposite_opposite, Option.map_id',
    Option.map_some] using hh

end GridHardness.LatticeRouteRuns

namespace GridHardness.SignedTentacle.CardinalRunChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem terminal_axis_direction (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    (s.frame.axisDirection::rs.map Prod.fst).getLast? =
      some (RunChain.terminal s length (requests s length rs)).1.frame.axisDirection := by
  induction rs generalizing s length with
  | nil => rfl
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
    have h := ih t n hc'
    rw [ht] at h
    simp only [List.map_cons, List.getLast?_cons, h, Option.getD_some,
      requests, RunChain.terminal]
    rfl

theorem drawingFrom_last_direction (s : RunState) (length : Nat) (rs : List Run)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2)) :
    (s.frame.axisDirection::rs.map Prod.fst).getLast? =
      some (drawingFrom s length rs).lastFrame.axisDirection := by
  rw [(drawingFrom_terminal s length rs).1]
  exact terminal_axis_direction s length rs hc

end GridHardness.SignedTentacle.CardinalRunChain
