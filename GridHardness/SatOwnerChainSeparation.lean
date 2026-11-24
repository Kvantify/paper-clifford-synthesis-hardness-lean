/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDockCorridorSeparation
public import GridHardness.SignedTentacleTransform

/-!
# SAT Owner Chain Separation

Pairwise clearance for owner-initialized corridor chains. The global
argument reduces any possible contact to the two distinct straight owner
docks, whose exact local geometry rules it out.
-/

public section

namespace GridHardness.SatDockCorridors
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Quantitative containment and initial-strip locality discharge global
pairwise clearance for arbitrary drawings of the actual dock corridors. -/
theorem chain_distance_of_locality (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (d g : Drawing) (n m : Nat)
    (hcoverD : ∀ p ∈d.points, ∃ q ∈route x hw e, IntegerGrid.manhattan p q ≤2)
    (hcoverG : ∀ p ∈g.points, ∃ q ∈route x hw f, IntegerGrid.manhattan p q ≤2)
    (hlocalD : ∀ p ∈d.points,
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (owner x e)) p ≤7 →
      p ∈strip ((SatNineClusterPlacement.frame x hw (owner x e)).comp
        (NineClusterAttachment.dock true (side x hw e false))) n)
    (hlocalG : ∀ p ∈g.points,
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (owner x f)) p ≤7 →
      p ∈strip ((SatNineClusterPlacement.frame x hw (owner x f)).comp
        (NineClusterAttachment.dock true (side x hw f false))) m)
    (p q : Point) (hp : p ∈d.points) (hq : q ∈g.points) :
    2≤IntegerGrid.manhattan p q := by
  by_contra hd
  have hpq : IntegerGrid.manhattan p q≤1 := by omega
  obtain ⟨u,hu,hpu⟩ := hcoverD p hp
  obtain ⟨v,hv,hqv⟩ := hcoverG q hq
  have hup : IntegerGrid.manhattan u p≤2 := by simpa only [IntegerGrid.manhattan_comm] using hpu
  have hvq : IntegerGrid.manhattan v q≤2 := by simpa only [IntegerGrid.manhattan_comm] using hqv
  obtain ⟨ho,hplocal,hqlocal⟩ := near_shared_owner x hw e f hef u v p q hu hv hup hvq hpq
  have hps := hlocalD p hp hplocal
  have hqs := hlocalG q hq hqlocal
  rw [strip_comp] at hps hqs
  rw [← ho] at hqs
  have hdist := NineClusterDockGeometry.frame_dock_distance
    (SatNineClusterPlacement.frame x hw (owner x e)) true true
    (side x hw e false) (side x hw f false) (owner_sides_ne x hw e f hef ho)
    n m p q hps hqs
  omega

end GridHardness.SatDockCorridors
