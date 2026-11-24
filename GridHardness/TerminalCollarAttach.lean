/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarMatch

/-!
# Terminal Collar Attach

Recipient attachment in global coordinates. Translate the preceding
chain to the recipient anchor, select its lane phase, graft the certified
collar, and translate back. All prior vertices and start labels are
preserved, and the complete target interface is a singleton.
-/

@[expose] public section

namespace GridHardness.TerminalCollarAttach
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def shift (a : Point) : Frame := ⟨true,false,false,a⟩
def unshift (a : Point) : Frame := ⟨true,false,false,(-a.1,-a.2)⟩

@[simp] theorem shift_unshift (a p : Point) : (shift a).map ((unshift a).map p)=p := by
  rcases p with ⟨x,y⟩
  simp [shift,unshift,Frame.map,place,sign]

@[simp] theorem unshift_shift (a p : Point) : (unshift a).map ((shift a).map p)=p := by
  rcases p with ⟨x,y⟩
  simp [shift,unshift,Frame.map,place,sign]

def localize (a : Point) (old : Drawing) : Drawing := Drawing.transform (unshift a) old

theorem localize_valid (a : Point) (old : Drawing) (h : old.Valid) : (localize a old).Valid :=
  Drawing.transform_valid _ _ h

theorem localize_lastFrame (a : Point) (old : Drawing) :
    (localize a old).lastFrame=(unshift a).comp old.lastFrame := by cases old <;> rfl

theorem localize_lastLength (a : Point) (old : Drawing) :
    (localize a old).lastLength=old.lastLength := by cases old <;> rfl

theorem localize_direction (a : Point) (old : Drawing) :
    (localize a old).lastFrame.axisDirection=old.lastFrame.axisDirection := by
  rw [localize_lastFrame]
  generalize old.lastFrame=f
  rcases f with ⟨h,x,y,o⟩
  cases h <;> cases x <;> cases y <;> rfl

def phase (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) : Bool :=
  TerminalCollarMatch.chosenPhase (localize a old) s lane

def attach (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) : Drawing :=
  Drawing.transform (shift a)
    (TerminalCollarMatched.attach (localize a old) s (phase a old s lane))

theorem transform_graft (f : Frame) (old d : Drawing) :
    Drawing.transform f (Drawing.graft old d)=
      Drawing.graft (Drawing.transform f old) (Drawing.transform f d) := by
  induction d with
  | base g n => rfl
  | attach d g n ih => simp only [Drawing.graft,Drawing.transform,ih]

theorem shift_unshift_comp (a : Point) (f : Frame) :
    (shift a).comp ((unshift a).comp f)=f := by
  rcases f with ⟨h,x,y,o⟩
  cases h <;> cases x <;> cases y <;>
    simp [shift,unshift,Frame.comp,Frame.map,place,sign]

theorem localize_restore (a : Point) (old : Drawing) :
    Drawing.transform (shift a) (localize a old)=old := by
  induction old with
  | base f n => simp only [localize,Drawing.transform,shift_unshift_comp]
  | attach d f n ih =>
    change Drawing.attach (Drawing.transform (shift a) (localize a d))
      ((shift a).comp ((unshift a).comp f)) n=Drawing.attach d f n
    rw [ih,shift_unshift_comp]

/-- The implementation retains the old signed frames themselves,
not merely their point sets. This preserves syntactic owner docking. -/
theorem attach_eq_graft (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    attach a old s lane=Drawing.graft old
      (Drawing.transform (shift a) (TerminalCollarMatched.phaseDrawing s (phase a old s lane))) := by
  rw [attach,TerminalCollarMatched.attach,transform_graft,localize_restore]

def BoxLocality (a : Point) (old : Drawing) : Prop := ∀ p∈old.points,
  a.1-11≤p.1 ∧ p.1≤a.1+11 ∧ a.2-11≤p.2 ∧ p.2≤a.2+11 →
    p∈strip old.lastFrame old.lastLength

theorem localized_tip (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s)) :
    (localize a old).tip lane=TerminalCollarMatch.innerPoint s := by
  rw [localize,Drawing.transform_tip,he,unshift_shift]

theorem localized_locality (a : Point) (old : Drawing) (hl : BoxLocality a old) :
    ∀ p∈(localize a old).points, -11≤p.1 ∧ p.1≤11 ∧ -11≤p.2 ∧ p.2≤11 →
      p∈strip (localize a old).lastFrame (localize a old).lastLength := by
  intro p hp hb
  rw [localize,Drawing.transform_points] at hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hqb : a.1-11≤q.1 ∧ q.1≤a.1+11 ∧ a.2-11≤q.2 ∧ q.2≤a.2+11 := by
    simp [unshift,Frame.map,place,sign] at hb
    omega
  rw [localize_lastFrame,localize_lastLength,strip_comp]
  exact Finset.mem_image.mpr ⟨q,hl q hq hqb,rfl⟩

theorem aligned (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s)) :
    Aligned (localize a old).tip (TerminalCollarMatched.phaseDrawing s (phase a old s lane)).baseTip :=
  TerminalCollarMatch.tip_aligned (localize a old) s lane
    ((localize_direction a old).trans hd) (localized_tip a old s lane he)

theorem localClear (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) :
    TerminalCollarMatched.LocalClear (localize a old) s (phase a old s lane) :=
  TerminalCollarMatch.localClear_of_terminal_locality (localize a old) s lane
    ((localize_direction a old).trans hd) (localized_tip a old s lane he)
    (localized_locality a old hl)

/-- No local contact or clearance assumption remains beyond the
terminal-strip locality supplied by the preceding route geometry. -/
theorem valid (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) : (attach a old s lane).Valid := by
  apply Drawing.transform_valid
  exact TerminalCollarMatched.attach_valid _ _ _ (localize_valid a old ho)
    (aligned a old s lane hd he) (localClear a old s lane hd he hl)

theorem start (a : Point) (old : Drawing) (s : Fin 4) (lane r : Fin 2) :
    (attach a old s lane).start r=old.start r := by
  rw [attach,Drawing.transform_start,TerminalCollarMatched.attach_start,
    localize,Drawing.transform_start,shift_unshift]

theorem tip (a : Point) (old : Drawing) (s : Fin 4) (lane r : Fin 2) :
    (attach a old s lane).tip r=(shift a).map (TerminalCollarRotations.tip s r) := by
  rw [attach,Drawing.transform_tip,TerminalCollarMatched.attach_tip,
    TerminalCollarMatched.phase_tip_coordinates]

/-- The earlier chain is retained point for point; only the four
translated receiving strips are added. -/
theorem points (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    (attach a old s lane).points=old.points ∪
      (TerminalCollarMatched.tail s (phase a old s lane)).image (shift a).map := by
  rw [attach,Drawing.transform_points,TerminalCollarMatched.attach_points,
    Finset.image_union,localize,Drawing.transform_points,Finset.image_image]
  simp only [Function.comp_def,shift_unshift]
  congr 1
  ext p
  simp

theorem old_subset (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    old.points⊆(attach a old s lane).points := by
  rw [points]
  exact Finset.subset_union_left

theorem new_radius (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    {p : Point} (hp : p ∈ (attach a old s lane).points) (ho : p ∉ old.points) :
    IntegerGrid.manhattan a p≤14 := by
  rw [points,Finset.mem_union] at hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (hp.resolve_left ho)
  have hd := (shift a).distance (0,0) q
  rw [Frame.map_zero] at hd
  exact hd.trans_le (TerminalCollarMatched.tail_radius s _ q hq)

theorem card_le (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) : (attach a old s lane).points.card≤old.points.card+34 := by
  rw [attach,Drawing.transform_points,Finset.card_image_of_injective _ (shift a).injective]
  have h := TerminalCollarMatched.attach_card_le _ s (phase a old s lane)
    (localize_valid a old ho) (aligned a old s lane hd he) (localClear a old s lane hd he hl)
  simpa only [localize,Drawing.transform_points,
    Finset.card_image_of_injective _ (unshift a).injective] using h

theorem cluster_disjoint (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) :
    Disjoint (TwoClusterAssembly.cluster ((shift a).comp TerminalCollar.clusterFrame))
      (attach a old s lane).points := by
  rw [TwoClusterAssembly.cluster_comp,attach,Drawing.transform_points]
  apply (Finset.disjoint_image (shift a).injective).mpr
  exact TerminalCollarMatched.attach_cluster_disjoint _ _ _ (localClear a old s lane hd he hl)

/-- The actual placed recipient cluster has exactly the required
boundary edge to the complete old-chain-plus-collar drawing. -/
theorem boundary (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) :
    TwoClusterAssembly.boundary
      (TwoClusterAssembly.cluster ((shift a).comp TerminalCollar.clusterFrame))
      (attach a old s lane).points =
        {(TwoClusterAssembly.corner ((shift a).comp TerminalCollar.clusterFrame) s,
          (attach a old s lane).tip 0)} := by
  rw [TwoClusterAssembly.cluster_comp,attach,Drawing.transform_points,
    TwoClusterAssembly.boundary_transform,
    TerminalCollarMatched.attach_boundary _ _ _ (localize_valid a old ho)
      (aligned a old s lane hd he) (localClear a old s lane hd he hl),
    Finset.image_singleton,TwoClusterAssembly.corner_comp,Drawing.transform_tip]

/-- A point in the clearance box is at most thirty-two steps from any
of the four prescribed inner endpoints. -/
theorem box_endpoint_distance (a p : Point) (s : Fin 4)
    (hb : a.1 - 11 ≤ p.1 ∧ p.1 ≤ a.1 + 11 ∧ a.2 - 11 ≤ p.2 ∧ p.2 ≤ a.2 + 11) :
    IntegerGrid.manhattan p ((shift a).map (TerminalCollarMatch.innerPoint s))≤32 := by
  fin_cases s <;> simp [shift,Frame.map,place,sign,TerminalCollarMatch.innerPoint,
    IntegerGrid.manhattan] <;> omega

/-- Interface to the endpoint-locality theorem for the compiled long
runs. Its strict distance test holds uniformly throughout the box. -/
theorem boxLocality_of_close (a : Point) (old : Drawing) (s : Fin 4)
    (h : ∀ p ∈ old.points,
      IntegerGrid.manhattan p ((shift a).map (TerminalCollarMatch.innerPoint s)) + 2<52 →
        p ∈ strip old.lastFrame old.lastLength) : BoxLocality a old := by
  intro p hp hb
  have hd := box_endpoint_distance a p s hb
  exact h p hp (by omega)

end GridHardness.TerminalCollarAttach
