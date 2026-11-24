/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarRotations

/-!
# Terminal Collar Matched

Recipient collars with their incoming lanes matched to the fixed
horizontal phase of the nine-cluster placement. All four start on the
radius-sixteen boundary. The bottom and top templates use slightly
different detour heights; a rigid rotation of one template alone would
leave their incoming lanes shifted by one lattice unit. These are finite
local certificates, not a construction of the whole SAT grid layout.
-/

@[expose] public section

namespace GridHardness.TerminalCollarMatched
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 8192

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

/-- An eastbound incoming strip, followed by north/east/south/east
strips. Only the four concrete parameter choices below are used. -/
def west (y : Int) (height n : Nat) : Drawing :=
  .attach
    (.attach
      (.attach
        (.attach
          (.base ⟨true,false,false,(-8-(n : Int),y)⟩ n)
          ⟨false,false,false,(-8,y)⟩ ((height : Int)-y).toNat)
        ⟨true,false,false,(-8,(height : Int))⟩ 3)
      ⟨false,true,false,(-5,(height : Int)+1)⟩ (height+2))
    TerminalCollar.terminalFrame 4

/-- The Boolean chooses either side of the ideal corridor axis for its
second lane. The longitudinal cut remains at radius sixteen. -/
def phaseTemplate (s : Fin 4) (b : Bool) : Drawing :=
  let δ : Int := if b then 1 else 0
  ![west (-δ) 3 8,west (1-δ) 4 7,west (-δ) 3 6,west (-1-δ) 3 7] s

def template (s : Fin 4) : Drawing := phaseTemplate s false

def phaseDrawing (s : Fin 4) (b : Bool) : Drawing :=
  Drawing.transform (TerminalCollarRotations.rotation s) (phaseTemplate s b)

/-- Left, bottom, right, and top collars around the same odd cluster. -/
def drawing (s : Fin 4) : Drawing :=
  Drawing.transform (TerminalCollarRotations.rotation s) (template s)

theorem template_valid : ∀ s : Fin 4, (template s).Valid := by decide +kernel

theorem valid (s : Fin 4) : (drawing s).Valid :=
  Drawing.transform_valid _ _ (template_valid s)

/-- Every initial rung is on the radius-sixteen boundary, with the
transverse lanes of the corresponding even owner's outgoing corridor. -/
theorem start_coordinates (s : Fin 4) (r : Fin 2) :
    (drawing s).start r =
      ![(-16,(r.val : Int)),(-(r.val : Int),-16),
        (16,-(r.val : Int)),((r.val : Int),16)] s := by
  fin_cases s <;> fin_cases r <;> rfl

/-- Changing the upper detour leaves the recipient's lane-zero dock
unchanged, including its lane ordering. -/
theorem tip_coordinates (s : Fin 4) (r : Fin 2) :
    (drawing s).tip r =
      ![(-1,-1-(r.val : Int)),(2+(r.val : Int),-2),
        (3,1+(r.val : Int)),(-(r.val : Int),2)] s := by
  fin_cases s <;> fin_cases r <;> rfl

theorem tip_eq_rotation (s : Fin 4) (r : Fin 2) :
    (drawing s).tip r = TerminalCollarRotations.tip s r := by
  rw [tip_coordinates,TerminalCollarRotations.tip_coordinates]

/-- The exact half-sizes also record a uniform bound for the finite
rectangular detours; the shorter right-hand collar has two fewer rungs. -/
theorem halfSize (s : Fin 4) : (drawing s).halfSize = ![24,24,22,24] s := by
  fin_cases s <;> rfl

theorem card (s : Fin 4) : (drawing s).points.card = ![48,48,44,48] s := by
  rw [Drawing.card _ (valid s),halfSize]
  fin_cases s <;> rfl

theorem card_le (s : Fin 4) : (drawing s).points.card ≤ 48 := by
  rw [card]
  fin_cases s <;> decide

theorem bounds : ∀ s : Fin 4, ∀ p ∈ (drawing s).points,
    -16 ≤ p.1 ∧ p.1 ≤ 16 ∧ -16 ≤ p.2 ∧ p.2 ≤ 16 := by decide +kernel

/-- The extra lane reaches one step beyond the cardinal radius in the
Manhattan metric, while staying in the radius-sixteen coordinate square. -/
theorem radius : ∀ s : Fin 4, ∀ p ∈ (drawing s).points,
    IntegerGrid.manhattan (0,0) p ≤ 17 := by decide +kernel

theorem distance : ∀ s t : Fin 4, s ≠ t →
    ∀ p ∈ (drawing s).points, ∀ q ∈ (drawing t).points,
      3 ≤ IntegerGrid.manhattan p q := by decide +kernel

/-- The phase corrections preserve separation of every pair of sides. -/
theorem apart (s t : Fin 4) (hst : s ≠ t) :
    ClusterStar.Apart (drawing s).points (drawing t).points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := distance s t hst p hp p hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := distance s t hst p hp q hq
    change IntegerGrid.manhattan p q = 1 at ha
    omega

theorem cluster_disjoint : ∀ s : Fin 4,
    Disjoint (TwoClusterAssembly.cluster TerminalCollar.clusterFrame) (drawing s).points := by
  decide +kernel

/-- All points in the complete five-strip local collar are included
when certifying the sole induced edge to the odd target cluster. -/
theorem boundary_singleton : ∀ s : Fin 4,
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (drawing s).points =
        {(TwoClusterAssembly.corner TerminalCollar.clusterFrame s,(drawing s).tip 0)} := by
  decide +kernel

theorem tip_adjacent (s : Fin 4) :
    lattice.Adj (TwoClusterAssembly.corner TerminalCollar.clusterFrame s) ((drawing s).tip 0) := by
  have hm : (TwoClusterAssembly.corner TerminalCollar.clusterFrame s,(drawing s).tip 0) ∈
      TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
        (drawing s).points := by rw [boundary_singleton]; simp
  exact (Finset.mem_filter.mp hm).2

/-- Translation/rotation of a matched collar preserves its validity. -/
theorem placed_valid (f : Frame) (s : Fin 4) :
    (Drawing.transform f (drawing s)).Valid := Drawing.transform_valid _ _ (valid s)

theorem placed_boundary (f : Frame) (s : Fin 4) :
    TwoClusterAssembly.boundary
      (TwoClusterAssembly.cluster (f.comp TerminalCollar.clusterFrame))
      (Drawing.transform f (drawing s)).points =
        {(TwoClusterAssembly.corner (f.comp TerminalCollar.clusterFrame) s,
          (Drawing.transform f (drawing s)).tip 0)} := by
  rw [TwoClusterAssembly.cluster_comp,Drawing.transform_points,
    TwoClusterAssembly.boundary_transform,boundary_singleton,Finset.image_singleton,
    TwoClusterAssembly.corner_comp,Drawing.transform_tip]

/-- Both possible transverse lane phases give valid five-strip collars. -/
theorem phase_template_valid : ∀ (s : Fin 4) (b : Bool), (phaseTemplate s b).Valid := by
  decide +kernel

theorem phase_valid (s : Fin 4) (b : Bool) : (phaseDrawing s b).Valid :=
  Drawing.transform_valid _ _ (phase_template_valid s b)

theorem phase_start_coordinates (s : Fin 4) (b : Bool) (r : Fin 2) :
    (phaseDrawing s b).start r =
      let δ : Int := if b then 1 else 0
      ![(-16,(r.val : Int)-δ),(δ-(r.val : Int),-16),
        (16,δ-(r.val : Int)),((r.val : Int)-δ,16)] s := by
  fin_cases s <;> cases b <;> fin_cases r <;> rfl

/-- The alternate entry lane changes no recipient tip or corner. -/
theorem phase_tip_coordinates (s : Fin 4) (b : Bool) (r : Fin 2) :
    (phaseDrawing s b).tip r = TerminalCollarRotations.tip s r := by
  fin_cases s <;> cases b <;> fin_cases r <;> rfl

theorem phase_halfSize (s : Fin 4) (b : Bool) :
    (phaseDrawing s b).halfSize = ![24,24,22,24] s + if b then 1 else 0 := by
  fin_cases s <;> cases b <;> rfl

theorem phase_card (s : Fin 4) (b : Bool) :
    (phaseDrawing s b).points.card = ![48,48,44,48] s + if b then 2 else 0 := by
  rw [Drawing.card _ (phase_valid s b),phase_halfSize]
  fin_cases s <;> cases b <;> rfl

theorem phase_card_le (s : Fin 4) (b : Bool) : (phaseDrawing s b).points.card ≤ 50 := by
  rw [phase_card]
  fin_cases s <;> cases b <;> decide

theorem phase_bounds : ∀ (s : Fin 4) (b : Bool), ∀ p ∈ (phaseDrawing s b).points,
    -16 ≤ p.1 ∧ p.1 ≤ 16 ∧ -16 ≤ p.2 ∧ p.2 ≤ 16 := by decide +kernel

theorem phase_radius : ∀ (s : Fin 4) (b : Bool), ∀ p ∈ (phaseDrawing s b).points,
    IntegerGrid.manhattan (0,0) p ≤ 17 := by decide +kernel

set_option maxHeartbeats 1000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
/-- Different sides remain separated for every independent choice of
the incoming corridor's transverse lane phase. -/
theorem phase_distance : ∀ (s t : Fin 4) (b c : Bool), s ≠ t →
    ∀ p ∈ (phaseDrawing s b).points, ∀ q ∈ (phaseDrawing t c).points,
      3 ≤ IntegerGrid.manhattan p q := by decide +kernel

theorem phase_apart (s t : Fin 4) (b c : Bool) (hst : s ≠ t) :
    ClusterStar.Apart (phaseDrawing s b).points (phaseDrawing t c).points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := phase_distance s t b c hst p hp p hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := phase_distance s t b c hst p hp q hq
    change IntegerGrid.manhattan p q = 1 at ha
    omega

theorem phase_cluster_disjoint : ∀ (s : Fin 4) (b : Bool),
    Disjoint (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (phaseDrawing s b).points := by decide +kernel

theorem phase_boundary_singleton : ∀ (s : Fin 4) (b : Bool),
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster TerminalCollar.clusterFrame)
      (phaseDrawing s b).points =
        {(TwoClusterAssembly.corner TerminalCollar.clusterFrame s,(phaseDrawing s b).tip 0)} := by
  decide +kernel

end GridHardness.TerminalCollarMatched
