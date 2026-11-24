/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarMatchedExtension
public import GridHardness.SignedTentacleCardinalFrames
public import GridHardness.SignedTentacleChain

/-!
# Terminal Collar Match

Select the receiving collar from a signed final strip. The tracked
ideal terminal lane and the inward direction determine its transverse
phase explicitly. Endpoint locality then establishes the required finite
clearance condition for the entire preceding drawing.
-/

@[expose] public section

namespace GridHardness.TerminalCollarMatch
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open TerminalCollarMatched
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def innerPoint : Fin 4 → Point := ![(-8,0),(0,-9),(10,0),(0,9)]

/-- Relative lane reflection, including the orientation of the chosen
cluster side. The side index is also its inward cardinal direction. -/
def phaseFor (f : Frame) (s : Fin 4) (lane : Fin 2) : Bool :=
  decide (lane=1) ^^ f.reverseY ^^ decide (s=1 ∨ s=2)

/-- Explicit coordinate membership for every incoming template strip. -/
theorem incoming_coordinates (s : Fin 4) (b : Bool) (p : Point) :
    p∈incoming s b ↔
      let δ : Int := if b then 1 else 0
      ![(-16≤p.1 ∧ p.1≤-8 ∧ -δ≤p.2 ∧ p.2≤1-δ),
        (δ-1≤p.1 ∧ p.1≤δ ∧ -16≤p.2 ∧ p.2≤-9),
        (10≤p.1 ∧ p.1≤16 ∧ δ-1≤p.2 ∧ p.2≤δ),
        (-δ≤p.1 ∧ p.1≤1-δ ∧ 9≤p.2 ∧ p.2≤16)] s := by
  fin_cases s <;> cases b <;>
    simp [incoming,phaseDrawing,phaseTemplate,Drawing.basePoints,Drawing.baseFrame,
      Drawing.baseLength,Drawing.transform,west,TerminalCollarRotations.rotation,
      Frame.comp,mem_strip_iff,Frame.unmap,Frame.map,place,sign] <;> omega

/-- Either ordering of the final rung is handled without relabeling
the old drawing's start or its corner-attached lane. -/
theorem far_aligned (f : Frame) (n : Nat) (s : Fin 4) (lane : Fin 2)
    (hd : f.axisDirection = s) (he : far f n lane = innerPoint s) :
    Aligned (far f n) (phaseDrawing s (phaseFor f s lane)).baseTip := by
  rcases f with ⟨h,rx,ry,⟨x,y⟩⟩
  fin_cases s <;> cases h <;> cases rx <;> cases ry <;> fin_cases lane
  all_goals simp [Frame.axisDirection] at hd
  all_goals simp [SignedTentacle.far,Frame.map,place,sign,innerPoint,Prod.mk.injEq] at he
  all_goals simp [Aligned,baseTip_coordinates,phaseFor,SignedTentacle.far,Frame.map,place,sign,
    Prod.mk.injEq] <;> omega

/-- Once the final rung is at the prescribed inner cut, all points of
its inward strip near the target lie in the matching incoming template.
The preceding strip length is arbitrary. -/
theorem strip_near_box (f : Frame) (n : Nat) (s : Fin 4) (lane : Fin 2)
    (hd : f.axisDirection = s) (he : far f n lane = innerPoint s)
    {p : Point} (hp : p ∈ strip f n)
    (hb : -11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11) :
    p∈incoming s (phaseFor f s lane) := by
  rw [incoming_coordinates]
  have hm := (mem_strip_iff f n p).mp hp
  rcases f with ⟨h,rx,ry,⟨x,y⟩⟩
  fin_cases s <;> cases h <;> cases rx <;> cases ry <;> fin_cases lane
  all_goals simp [Frame.axisDirection] at hd
  all_goals simp [SignedTentacle.far,Frame.map,place,sign,innerPoint,Prod.mk.injEq] at he
  all_goals simp [Frame.unmap,sign] at hm
  all_goals simp [phaseFor] <;> omega

def chosenPhase (old : Drawing) (s : Fin 4) (lane : Fin 2) : Bool :=
  phaseFor old.lastFrame s lane

theorem tip_aligned (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s) (he : old.tip lane = innerPoint s) :
    Aligned old.tip (phaseDrawing s (chosenPhase old s lane)).baseTip := by
  rw [old.tip_last] at he ⊢
  exact far_aligned old.lastFrame old.lastLength s lane hd he

/-- Endpoint locality is sufficient for the finite clearance test; no
additional overlap or induced-edge assumptions are left to the caller. -/
theorem localClear_of_terminal_locality (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s) (he : old.tip lane = innerPoint s)
    (hl : ∀ p ∈ old.points, -11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11 →
      p ∈ strip old.lastFrame old.lastLength) :
    LocalClear old s (chosenPhase old s lane) := by
  apply localClear_of_box
  intro p hp hb
  apply strip_near_box old.lastFrame old.lastLength s lane hd
  · simpa only [old.tip_last] using he
  · exact hl p hp hb
  · exact hb

/-- A selected receiver can be grafted using only the incoming
direction, the exact ideal endpoint, and terminal-strip locality. -/
theorem attach_valid (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = innerPoint s)
    (hl : ∀ p ∈ old.points, -11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11 →
      p ∈ strip old.lastFrame old.lastLength) :
    (TerminalCollarMatched.attach old s (chosenPhase old s lane)).Valid :=
  TerminalCollarMatched.attach_valid old s _ ho (tip_aligned old s lane hd he)
    (localClear_of_terminal_locality old s lane hd he hl)

theorem attach_boundary (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = innerPoint s)
    (hl : ∀ p ∈ old.points, -11 ≤ p.1 ∧ p.1 ≤ 11 ∧ -11 ≤ p.2 ∧ p.2 ≤ 11 →
      p ∈ strip old.lastFrame old.lastLength) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (TerminalCollarMatched.attach old s (chosenPhase old s lane)).points =
        {(TwoClusterAssembly.corner TerminalCollar.clusterFrame s,
          (TerminalCollarMatched.attach old s (chosenPhase old s lane)).tip 0)} :=
  TerminalCollarMatched.attach_boundary old s _ ho (tip_aligned old s lane hd he)
    (localClear_of_terminal_locality old s lane hd he hl)

end GridHardness.TerminalCollarMatch
