/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoClusterAssembly

/-!
# Cluster Star

An even-side nine-cluster region owns two selected incident tentacles
and optionally one unused tentacle. Only coordinate separation, signed-strip
validity and concrete docking are supplied; every spanning route is derived.
The unused tentacle is absorbed along the third reserved cluster edge.
-/

@[expose] public section

namespace GridHardness.ClusterStar
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

/-- Distinct incident tentacles have no common vertices or lattice edges. -/
def Apart (S T : Finset Point) : Prop :=
  Disjoint S T ∧ ∀ a ∈ S, ∀ b ∈ T, ¬lattice.Adj a b

instance (S T : Finset Point) : Decidable (Apart S T) := by unfold Apart; infer_instance

theorem Apart.symm {S T : Finset Point} (h : Apart S T) : Apart T S :=
  ⟨h.1.symm, fun _ ha _ hb hab => h.2 _ hb _ ha hab.symm⟩

structure Star where
  first : Drawing
  second : Drawing
  firstSide : Fin 4
  secondSide : Fin 4
  unused : Option (Fin 4 × Drawing)
  deriving DecidableEq

def Star.Valid (s : Star) : Prop :=
  s.first.Valid ∧ s.second.Valid ∧
  NineClusterAttachment.Docked true s.firstSide s.first ∧
  NineClusterAttachment.Docked true s.secondSide s.second ∧
  s.firstSide ≠ s.secondSide ∧ Apart s.first.points s.second.points ∧
  match s.unused with
  | none => True
  | some (side, d) => d.Valid ∧ NineClusterAttachment.Docked true side d ∧
      side ≠ s.firstSide ∧ side ≠ s.secondSide ∧
      Apart s.first.points d.points ∧ Apart s.second.points d.points

instance (s : Star) : Decidable s.Valid := by
  unfold Star.Valid
  cases s.unused <;> infer_instance

def Star.extraPoints (s : Star) : Finset Point :=
  match s.unused with | none => ∅ | some (_, d) => d.points

def Star.extraHalfSize (s : Star) : Nat :=
  match s.unused with | none => 0 | some (_, d) => d.halfSize

def Star.corePoints (s : Star) : Finset Point := NineClusterAttachment.points ∪ s.extraPoints

def Star.points (s : Star) : Finset Point := s.corePoints ∪ s.first.points ∪ s.second.points

/-- Route through the cluster and optional return branch, with both selected
cluster corners retained as endpoints. -/
theorem Star.core_route (s : Star) (h : s.Valid) :
    HasRoute s.corePoints (NineClusterAttachment.corner s.firstSide)
      (NineClusterAttachment.corner s.secondSide) := by
  rcases h with ⟨ha, hb, hda, hdb, hside, hsep, hu⟩
  cases he : s.unused with
  | none =>
    obtain ⟨p, hp, hc, _⟩ := NineClusterAttachment.cluster_route _ _ hside
    simpa only [Star.corePoints, Star.extraPoints, he, Finset.union_empty] using
      (show HasRoute NineClusterAttachment.points _ _ from ⟨p, hp, hc⟩)
  | some extra =>
    rcases extra with ⟨side, d⟩
    rw [he] at hu
    simpa only [Star.corePoints, Star.extraPoints, he] using
      NineClusterAttachment.cluster_with_return_route d hu.1 side s.firstSide s.secondSide
        hu.2.1 hside

/-- Disjointness needed by the two final path joins follows entirely from
cluster docking and pairwise geometric separation. -/
theorem Star.disjointness (s : Star) (h : s.Valid) :
    Disjoint s.first.points s.corePoints ∧
      Disjoint (s.first.points ∪ s.corePoints) s.second.points := by
  rcases h with ⟨ha, hb, hda, hdb, hside, hsep, hu⟩
  have haextra : Disjoint s.first.points s.extraPoints := by
    cases he : s.unused with
    | none => simp [Star.extraPoints, he]
    | some extra =>
      rcases extra with ⟨side, d⟩
      rw [he] at hu
      simpa only [Star.extraPoints, he] using hu.2.2.2.2.1.1
  have hbextra : Disjoint s.second.points s.extraPoints := by
    cases he : s.unused with
    | none => simp [Star.extraPoints, he]
    | some extra =>
      rcases extra with ⟨side, d⟩
      rw [he] at hu
      simpa only [Star.extraPoints, he] using hu.2.2.2.2.2.1
  exact ⟨Finset.disjoint_union_right.mpr ⟨hda.disjoint.symm, haextra⟩,
    Finset.disjoint_union_left.mpr ⟨hsep.1,
      Finset.disjoint_union_left.mpr ⟨hdb.disjoint, hbextra.symm⟩⟩⟩

theorem dock_color {d : Drawing} {side : Fin 4}
    (h : NineClusterAttachment.Docked true side d) : color (d.start 0) = 1 := by
  rw [h.starts]
  fin_cases side <;> decide

/-- Hamiltonian routing across the entire star. The selected outer tips
must have the even cluster's checkerboard color; the unused branch is
traversed as a return and needs no independently assumed route. -/
theorem Star.route (s : Star) (h : s.Valid) (r t : Fin 2)
    (hr : color (s.first.tip r) = 0) (ht : color (s.second.tip t) = 0) :
    HasRoute s.points (s.first.tip r) (s.second.tip t) := by
  have ha := s.first.cross h.1 0 r (by rw [dock_color h.2.2.1, hr]; decide)
  have hb := s.second.cross h.2.1 0 t (by rw [dock_color h.2.2.2.1, ht]; decide)
  have hleft : lattice.Adj (s.first.start 0) (NineClusterAttachment.corner s.firstSide) := by
    rw [h.2.2.1.starts]
    exact (NineClusterAttachment.dock_first_adjacent true s.firstSide).symm
  have hright : lattice.Adj (NineClusterAttachment.corner s.secondSide) (s.second.start 0) := by
    rw [h.2.2.2.1.starts]
    exact NineClusterAttachment.dock_first_adjacent true s.secondSide
  have hfirst := TwoClusterAssembly.route_join (route_reverse ha) (s.core_route h)
    (s.disjointness h).1 hleft
  have hfull := TwoClusterAssembly.route_join hfirst hb (s.disjointness h).2 hright
  simpa only [Star.points, Finset.union_comm s.first.points s.corePoints] using hfull

theorem Star.first_tip_mem (s : Star) (h : s.Valid) (r : Fin 2) : s.first.tip r ∈ s.points :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (s.first.tip_mem h.1 r))

theorem Star.second_tip_mem (s : Star) (h : s.Valid) (t : Fin 2) : s.second.tip t ∈ s.points :=
  Finset.mem_union_right _ (s.second.tip_mem h.2.1 t)

/-- The route is Hamiltonian in the actual finite induced grid. -/
theorem Star.hamiltonian (s : Star) (h : s.Valid) (r t : Fin 2)
    (hr : color (s.first.tip r) = 0) (ht : color (s.second.tip t) = 0) :
    ∃ p : (finiteGrid s.points).Walk
      ⟨s.first.tip r, s.first_tip_mem h r⟩ ⟨s.second.tip t, s.second_tip_mem h t⟩,
      p.IsHamiltonian := (hasRoute_iff_hamiltonian _ _).mp (s.route h r t hr ht)

theorem Star.extra_card (s : Star) (h : s.Valid) :
    s.extraPoints.card = 2*s.extraHalfSize ∧
      Disjoint NineClusterAttachment.points s.extraPoints := by
  cases he : s.unused with
  | none => simp [Star.extraPoints, Star.extraHalfSize, he]
  | some extra =>
    rcases extra with ⟨side, d⟩
    have hu := h.2.2.2.2.2.2
    rw [he] at hu
    simpa only [Star.extraPoints, Star.extraHalfSize, he] using
      And.intro (d.card hu.1) hu.2.1.disjoint

/-- One odd nine-cluster and two or three even tentacles, with no duplicated
vertices at the docks. -/
theorem Star.points_card (s : Star) (h : s.Valid) :
    s.points.card = 9 + 2*(s.first.halfSize + s.second.halfSize + s.extraHalfSize) := by
  have hc : NineClusterAttachment.points.card = 9 := by
    unfold NineClusterAttachment.points
    rw [Finset.card_image_of_injective _ NineCluster.point_injective]
    simp
  have hdis := s.disjointness h
  have hcore : s.corePoints.card = 9 + 2*s.extraHalfSize := by
    rw [Star.corePoints, Finset.card_union_of_disjoint (s.extra_card h).2, hc, (s.extra_card h).1]
  rw [Star.points, Finset.card_union_of_disjoint
    (by simpa only [Finset.union_comm s.corePoints s.first.points] using hdis.2),
    Finset.card_union_of_disjoint hdis.1.symm, hcore, s.first.card h.1, s.second.card h.2.1]
  omega

/-- Each terminal rung has exactly one vertex of the cluster's color. -/
theorem even_tip_exists (d : Drawing) (h : d.Valid) : ∃ r : Fin 2, color (d.tip r) = 0 := by
  have ha := adjacent_color_ne (d.geometry h).2.1.2.2.1
  have h0 := color_bounds (d.tip 0)
  have h1 := color_bounds (d.tip 1)
  by_cases hz : color (d.tip 0) = 0
  · exact ⟨0, hz⟩
  · exact ⟨1, by omega⟩

/-- Valid geometry alone supplies some admissible pair of outer tips. -/
theorem Star.hamiltonian_exists (s : Star) (h : s.Valid) :
    ∃ (r t : Fin 2) (p : (finiteGrid s.points).Walk
      ⟨s.first.tip r, s.first_tip_mem h r⟩ ⟨s.second.tip t, s.second_tip_mem h t⟩),
      p.IsHamiltonian := by
  obtain ⟨r, hr⟩ := even_tip_exists s.first h.1
  obtain ⟨t, ht⟩ := even_tip_exists s.second h.2.1
  obtain ⟨p, hp⟩ := s.hamiltonian h r t hr ht
  exact ⟨r, t, p, hp⟩

end GridHardness.ClusterStar
