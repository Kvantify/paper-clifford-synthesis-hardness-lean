/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarAttach

/-!
# Terminal Collar Separation

Clearance between receiving collars on distinct sides of one cluster.
The old chain need only satisfy the same terminal direction, endpoint,
and locality conditions used by recipient attachment.
-/

public section

namespace GridHardness.TerminalCollarSeparation
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open TerminalCollarAttach
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Inside the recipient guard box, the old drawing lies in its selected
finite receiving template, not merely in the final unbounded corridor. -/
theorem old_near_template (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) {p : Point} (hp : p ∈ old.points)
    (hb : a.1 - 11 ≤ p.1 ∧ p.1 ≤ a.1 + 11 ∧ a.2 - 11 ≤ p.2 ∧ p.2 ≤ a.2 + 11) :
    p∈(TerminalCollarMatched.phaseDrawing s (phase a old s lane)).points.image
      (shift a).map := by
  have hpb : -11≤((unshift a).map p).1 ∧ ((unshift a).map p).1≤11 ∧
      -11≤((unshift a).map p).2 ∧ ((unshift a).map p).2≤11 := by
    simp [unshift,Frame.map,place,sign]
    omega
  have hpo : (unshift a).map p∈(localize a old).points := by
    rw [localize,Drawing.transform_points]
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hps := localized_locality a old hl _ hpo hpb
  have htip := localized_tip a old s lane he
  rw [Drawing.tip_last] at htip
  have hi := TerminalCollarMatch.strip_near_box
    (localize a old).lastFrame (localize a old).lastLength s lane
    ((localize_direction a old).trans hd) htip hps hpb
  apply Finset.mem_image.mpr
  refine ⟨(unshift a).map p,?_,shift_unshift a p⟩
  exact (TerminalCollarMatched.phaseDrawing s (phase a old s lane)).base_subset hi

/-- Added receiving strips are contained in the target-centered
square of radius ten. -/
theorem tail_bounds (a : Point) (s : Fin 4) (b : Bool) {p : Point}
    (hp : p ∈ (TerminalCollarMatched.tail s b).image (shift a).map) :
    a.1-10≤p.1 ∧ p.1≤a.1+10 ∧ a.2-10≤p.2 ∧ p.2≤a.2+10 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hb := TerminalCollarMatched.tail_bounds s b q hq
  simp [shift,Frame.map,place,sign]
  omega

/-- Distinct receiving sides remain three lattice steps apart for any
independent choices of transverse lane phase. -/
theorem tail_tail_distance (a : Point) (s t : Fin 4) (b c : Bool) (hst : s ≠ t)
    {p q : Point}
    (hp : p ∈ (TerminalCollarMatched.tail s b).image (shift a).map)
    (hq : q ∈ (TerminalCollarMatched.tail t c).image (shift a).map) :
    3≤IntegerGrid.manhattan p q := by
  obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.mp hq
  rw [(shift a).distance]
  exact TerminalCollarMatched.phase_distance s t b c hst p₀
    ((TerminalCollarMatched.phaseDrawing s b).tail_subset hp₀) q₀
    ((TerminalCollarMatched.phaseDrawing t c).tail_subset hq₀)

/-- A new receiving tail cannot meet or be adjacent to an old chain
entering another side of the same target cluster. -/
theorem tail_old_distance (a : Point) (s t : Fin 4) (b : Bool)
    (old : Drawing) (lane : Fin 2) (hst : s ≠ t)
    (hd : old.lastFrame.axisDirection = t)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint t))
    (hl : BoxLocality a old) {p q : Point}
    (hp : p ∈ (TerminalCollarMatched.tail s b).image (shift a).map)
    (hq : q ∈ old.points) : 2≤IntegerGrid.manhattan p q := by
  by_contra hn
  have hb := tail_bounds a s b hp
  have hqb : a.1-11≤q.1 ∧ q.1≤a.1+11 ∧ a.2-11≤q.2 ∧ q.2≤a.2+11 := by
    simp only [IntegerGrid.manhattan] at hn
    omega
  have hqt := old_near_template a old t lane hd he hl hq hqb
  obtain ⟨p₀,hp₀,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q₀,hq₀,rfl⟩ := Finset.mem_image.mp hqt
  have hdist := TerminalCollarMatched.phase_distance s t b (phase a old t lane)
    hst p₀ ((TerminalCollarMatched.phaseDrawing s b).tail_subset hp₀) q₀ hq₀
  rw [(shift a).distance] at hn
  omega

theorem tail_tail_apart (a : Point) (s t : Fin 4) (b c : Bool) (hst : s ≠ t) :
    ClusterStar.Apart ((TerminalCollarMatched.tail s b).image (shift a).map)
      ((TerminalCollarMatched.tail t c).image (shift a).map) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := tail_tail_distance a s t b c hst hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := tail_tail_distance a s t b c hst hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

theorem tail_old_apart (a : Point) (s t : Fin 4) (b : Bool)
    (old : Drawing) (lane : Fin 2) (hst : s ≠ t)
    (hd : old.lastFrame.axisDirection = t)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint t))
    (hl : BoxLocality a old) :
    ClusterStar.Apart ((TerminalCollarMatched.tail s b).image (shift a).map) old.points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := tail_old_distance a s t b old lane hst hd he hl hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := tail_old_distance a s t b old lane hst hd he hl hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

/-- Separation from both the retained chain and its new receiving tail. -/
theorem tail_attach_apart (a : Point) (s t : Fin 4) (b : Bool)
    (old : Drawing) (lane : Fin 2) (hst : s ≠ t)
    (hd : old.lastFrame.axisDirection = t)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint t))
    (hl : BoxLocality a old) :
    ClusterStar.Apart ((TerminalCollarMatched.tail s b).image (shift a).map)
      (attach a old t lane).points := by
  have h₁ := tail_old_apart a s t b old lane hst hd he hl
  have h₂ := tail_tail_apart a s t b (phase a old t lane) hst
  rw [points]
  constructor
  · exact Finset.disjoint_union_right.mpr ⟨h₁.1,h₂.1⟩
  · intro p hp q hq
    rcases Finset.mem_union.mp hq with hq|hq
    · exact h₁.2 p hp q hq
    · exact h₂.2 p hp q hq

/-- Attaching collars on distinct recipient sides preserves separation
of the two preceding chains. -/
theorem attach_apart (a : Point) (old₁ old₂ : Drawing)
    (s t : Fin 4) (lane₁ lane₂ : Fin 2) (hst : s ≠ t)
    (h₁d : old₁.lastFrame.axisDirection = s)
    (h₁e : old₁.tip lane₁ = (shift a).map (TerminalCollarMatch.innerPoint s))
    (h₁l : BoxLocality a old₁)
    (h₂d : old₂.lastFrame.axisDirection = t)
    (h₂e : old₂.tip lane₂ = (shift a).map (TerminalCollarMatch.innerPoint t))
    (h₂l : BoxLocality a old₂)
    (ho : ClusterStar.Apart old₁.points old₂.points) :
    ClusterStar.Apart (attach a old₁ s lane₁).points
      (attach a old₂ t lane₂).points := by
  have h₁ := tail_attach_apart a s t (phase a old₁ s lane₁) old₂ lane₂
    hst h₂d h₂e h₂l
  have h₂ := (tail_old_apart a t s (phase a old₂ t lane₂) old₁ lane₁
    (Ne.symm hst) h₁d h₁e h₁l).symm
  rw [points] at h₁
  rw [points,points]
  constructor
  · exact Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨ho.1,h₂.1⟩,h₁.1⟩
  · intro p hp q hq
    rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hq with hq|hq
      · exact ho.2 p hp q hq
      · exact h₂.2 p hp q hq
    · exact h₁.2 p hp q hq

end GridHardness.TerminalCollarSeparation
