/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatOwnerTentacles
public import GridHardness.SatOwnerChainSeparation

/-!
# SAT Owner Tentacle Separation

Pairwise and cluster clearance for the actual owner-initialized SAT
tentacles. Their verified centerline containment and computed endpoint
locality discharge all premises of the geometric separation arguments.
-/

public section

namespace GridHardness.SatOwnerTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxHeartbeats 2000000

/-- Distinct actual owner-initialized drawings have neither coincident
vertices nor unintended unit adjacencies, including at shared graph vertices. -/
theorem pairwise_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈(drawing x hw e).points) (hq : q ∈(drawing x hw f).points) :
    2≤IntegerGrid.manhattan p q :=
  SatDockCorridors.chain_distance_of_locality x hw e f hef (drawing x hw e) (drawing x hw f)
    (firstRun x hw e).2 (firstRun x hw f).2
    (centerline_distance x hw e) (centerline_distance x hw f)
    (first_strip_of_close x hw e) (first_strip_of_close x hw f) p q hp hq

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

/-- Unrelated graph anchors remain at least sixty-two steps from every
point of the actual drawing. -/
theorem unrelated_anchor_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : SatDockCorridors.Vertex x)
    (hvo : v ≠SatDockCorridors.owner x e) (hvr : v ≠SatDockCorridors.recipient x e)
    (q : Point) (hq : q ∈(drawing x hw e).points) :
    62≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v) q := by
  obtain ⟨p,hp,hqp⟩ := centerline_distance x hw e q hq
  have hd := SatDockCorridors.unrelated_anchor_clearance x hw e v hvo hvr p hp
  have ht := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) q p
  omega

/-- The entire actual drawing retains the fifty-nine-step margin from
all nine-clusters not incident to its edge. -/
theorem unrelated_cluster_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : SatDockCorridors.Vertex x)
    (hvo : v ≠SatDockCorridors.owner x e) (hvr : v ≠SatDockCorridors.recipient x e)
    (c q : Point) (hc : c ∈SatNineClusterPlacement.points x hw v)
    (hq : q ∈(drawing x hw e).points) : 59≤IntegerGrid.manhattan c q := by
  obtain ⟨p,hp,hqp⟩ := centerline_distance x hw e q hq
  exact SatDockCorridors.unrelated_cluster_clearance x hw e v hvo hvr p q c hp
    (by simpa only [IntegerGrid.manhattan_comm] using hqp) hc

/-- The receiving cluster has no contact with the original chain before
its dedicated collar is appended. -/
theorem recipient_cluster_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (c q : Point)
    (hc : c ∈SatNineClusterPlacement.points x hw (SatDockCorridors.recipient x e))
    (hq : q ∈(drawing x hw e).points) : 3≤IntegerGrid.manhattan c q := by
  obtain ⟨p,hp,hqp⟩ := centerline_distance x hw e q hq
  exact SatDockCorridors.recipient_cluster_clearance x hw e p q c hp
    (by simpa only [IntegerGrid.manhattan_comm] using hqp) hc

/-- All nonowner clusters are disjoint and nonadjacent to the actual
uncollared drawing. The recipient and unrelated vertices are both covered. -/
theorem nonowner_cluster_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : SatDockCorridors.Vertex x) (hvo : v ≠SatDockCorridors.owner x e) :
    ClusterStar.Apart (SatNineClusterPlacement.points x hw v) (drawing x hw e).points := by
  have hd (c q : Point) (hc : c∈SatNineClusterPlacement.points x hw v)
      (hq : q∈(drawing x hw e).points) : 2≤IntegerGrid.manhattan c q := by
    by_cases hvr : v=SatDockCorridors.recipient x e
    · subst v
      have h := recipient_cluster_clearance x hw e c q hc hq
      omega
    · have h := unrelated_cluster_clearance x hw e v hvo hvr c q hc hq
      omega
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := hd p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := hd p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

end GridHardness.SatOwnerTentacles
