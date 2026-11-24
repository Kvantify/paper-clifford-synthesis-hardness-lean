/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteTentacles
public import GridHardness.SatOwnerTentacleSeparation
public import GridHardness.TerminalCollarSeparation

/-!
# SAT Complete Tentacle Separation

Global clearance for the complete actual SAT tentacles. The
chain-separation lemmas, matched receiving templates, and scaled anchor spacing
cover every old/new pair of vertices without additional geometric premises.
-/

public section

namespace GridHardness.SatCompleteTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxHeartbeats 2000000

/-- A receiving tail and another edge's preceding chain remain disjoint
and nonadjacent, even when both terminate at the same graph vertex. -/
theorem tail_old_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈tail x hw e) (hq : q ∈(SatOwnerTentacles.drawing x hw f).points) :
    2≤IntegerGrid.manhattan p q := by
  by_cases hr : SatDockCorridors.recipient x e=SatDockCorridors.recipient x f
  · have ha : anchor x hw e=anchor x hw f := congrArg (SatNineClusterPlacement.anchor x hw) hr
    have hp' : p∈(TerminalCollarMatched.tail (side x hw e) (phase x hw e)).image
        (TerminalCollarAttach.shift (anchor x hw f)).map := by
      simpa only [tail,ha] using hp
    exact TerminalCollarSeparation.tail_old_distance (anchor x hw f)
      (side x hw e) (side x hw f) (phase x hw e) (SatOwnerTentacles.drawing x hw f)
      (lane x hw f) (SatDockCorridors.recipient_sides_ne x hw e f hef hr)
      (SatOwnerTentacles.endframe_direction x hw f) (aligned_tip x hw f)
      (locality x hw f) hp' hq
  · have hclear := SatOwnerTentacles.unrelated_anchor_clearance x hw f
      (SatDockCorridors.recipient x e) (Ne.symm (SatDockCorridors.owner_recipient_ne x f e)) hr q hq
    have hrad := tail_radius x hw e p hp
    have ht := IntegerGrid.manhattan_triangle (anchor x hw e) p q
    change 62≤IntegerGrid.manhattan (anchor x hw e) q at hclear
    omega

/-- Receiving tails on distinct edges are separated by at least three
steps. Different recipients have the stronger scale-induced margin. -/
theorem tail_tail_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈tail x hw e) (hq : q ∈tail x hw f) :
    3≤IntegerGrid.manhattan p q := by
  by_cases hr : SatDockCorridors.recipient x e=SatDockCorridors.recipient x f
  · have ha : anchor x hw e=anchor x hw f := congrArg (SatNineClusterPlacement.anchor x hw) hr
    have hp' : p∈(TerminalCollarMatched.tail (side x hw e) (phase x hw e)).image
        (TerminalCollarAttach.shift (anchor x hw f)).map := by
      simpa only [tail,ha] using hp
    exact TerminalCollarSeparation.tail_tail_distance (anchor x hw f)
      (side x hw e) (side x hw f) (phase x hw e) (phase x hw f)
      (SatDockCorridors.recipient_sides_ne x hw e f hef hr) hp' hq
  · have hd := LatticeSubdivision.scale_separation 64
      (fun he => hr (SatBipartiteDrawing.point_injective x hw he))
    change 64≤IntegerGrid.manhattan (anchor x hw e) (anchor x hw f) at hd
    have hpr := tail_radius x hw e p hp
    have hqr := tail_radius x hw f q hq
    have h₁ := IntegerGrid.manhattan_triangle (anchor x hw e) p (anchor x hw f)
    have h₂ := IntegerGrid.manhattan_triangle p q (anchor x hw f)
    rw [IntegerGrid.manhattan_comm q (anchor x hw f)] at h₂
    omega

/-- Every pair of distinct complete actual tentacles is disjoint and
nonadjacent throughout its owner chain and receiving collar. -/
theorem pairwise_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈(drawing x hw e).points) (hq : q ∈(drawing x hw f).points) :
    2≤IntegerGrid.manhattan p q := by
  rw [points,Finset.mem_union] at hp hq
  rcases hp with hp|hp <;> rcases hq with hq|hq
  · exact SatOwnerTentacles.pairwise_distance x hw e f hef p q hp hq
  · simpa only [IntegerGrid.manhattan_comm] using tail_old_distance x hw f e (Ne.symm hef) q p hq hp
  · exact tail_old_distance x hw e f hef p q hp hq
  · have h := tail_tail_distance x hw e f hef p q hp hq
    omega

theorem pairwise_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) : ClusterStar.Apart (drawing x hw e).points (drawing x hw f).points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := pairwise_distance x hw e f hef p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := pairwise_distance x hw e f hef p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

/-- A complete tentacle remains at least forty-seven lattice steps from
all clusters not incident to its graph edge. -/
theorem unrelated_cluster_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x)
    (hvo : v ≠SatDockCorridors.owner x e) (hvr : v ≠SatDockCorridors.recipient x e)
    (c q : Point) (hc : c ∈SatNineClusterPlacement.points x hw v)
    (hq : q ∈(drawing x hw e).points) : 47≤IntegerGrid.manhattan c q := by
  rw [points,Finset.mem_union] at hq
  rcases hq with hq|hq
  · have h := SatOwnerTentacles.unrelated_cluster_clearance x hw e v hvo hvr c q hc hq
    omega
  · exact tail_cluster_distance x hw e v hvr c q hc hq

theorem unrelated_cluster_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x)
    (hvo : v ≠SatDockCorridors.owner x e) (hvr : v ≠SatDockCorridors.recipient x e) :
    ClusterStar.Apart (SatNineClusterPlacement.points x hw v) (drawing x hw e).points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := unrelated_cluster_clearance x hw e v hvo hvr p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := unrelated_cluster_clearance x hw e v hvo hvr p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

end GridHardness.SatCompleteTentacles
