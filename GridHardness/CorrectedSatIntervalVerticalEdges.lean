/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetainedEdges
public import GridHardness.SatCrossingRouting

/-!
# Corrected SAT Interval Vertical Edges

Endpoint identities for vertical continuation intervals in the actual
two-sided sweep. The four lanes alternate direction. A cut retains the old
endpoint on each outer boundary and installs the appropriate retained row
port on its new inner boundary. These identities concern the actual registry,
not an assumed drawing or a promised graph interface.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.VerticalEdges
open XorLineRegistry XorLineSchedule XorLine GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- `true` refers to the lower end of an interval, `false` to its upper end.
The Boolean component of a slot still denotes target/source as usual. -/
def boundarySlot (lower : Bool) (r : Fin 4) : Slot :=
  (r, if lower then BundleSegments.towardTrue r else !BundleSegments.towardTrue r)

/-- The crossing port attached to the named boundary of an adjacent interval.
The lower endpoint of an interval is on the upper side of its crossing. -/
def boundaryPort (lower : Bool) (r : Fin 4) : SatCrossingHorizontal.RetainedVertex :=
  ⟨row r !(boundarySlot lower r).2,trivial⟩

theorem towardTrue_eq_even (r : Fin 4) :
    BundleSegments.towardTrue r = decide (r.val % 2 = 0) := by
  fin_cases r <;> rfl

theorem boundarySlot_opposite (lower : Bool) (r : Fin 4) :
    (boundarySlot (!lower) r).2 = !(boundarySlot lower r).2 := by
  cases lower <;> simp [boundarySlot]

theorem boundaryPort_even (lower : Bool) (r : Fin 4) (he : r.val % 2 = 0) :
    (boundaryPort lower r).val =
      if lower then inputPort 4 (.inr r) else outputPort 4 (.inr r) := by
  cases lower <;> simp [boundaryPort,boundarySlot,towardTrue_eq_even,he,inputPort,outputPort]

theorem boundaryPort_odd (lower : Bool) (r : Fin 4) (he : r.val % 2 ≠ 0) :
    (boundaryPort lower r).val =
      if lower then outputPort 4 (.inr r) else inputPort 4 (.inr r) := by
  cases lower <;> simp [boundaryPort,boundarySlot,towardTrue_eq_even,he,inputPort,outputPort]

private theorem outer_tag (lower : Bool) (r : Fin 4) :
    BundleSegments.endpointTag BundleSegments.towardTrue (lower,boundarySlot lower r) =
      .inl (boundarySlot lower r) := by
  fin_cases r <;> cases lower <;> rfl

private theorem inner_tag (lower : Bool) (r : Fin 4) :
    BundleSegments.endpointTag BundleSegments.towardTrue (lower,boundarySlot (!lower) r) =
      .inr (r,!(boundarySlot (!lower) r).2) := by
  fin_cases r <;> cases lower <;> rfl

variable {n : Nat}

/-- Each side of a cut keeps its old outer boundary endpoint under the exact
vertex-name transport used by the global sweep. -/
theorem split_outer_endpoint (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (lower : Bool) (r : Fin 4) :
    endpoint ((s.cross a line height hc).positioned.registry.bundles (.inr lower))
      (boundarySlot lower r) =
    crossLift s a line height hc
      (endpoint (s.positioned.registry.bundles (s.select line height hc).val)
        (boundarySlot lower r)) := by
  change endpoint (BundleSegments.side (s.positioned.registry.bundles _)
    (s.positioned.registry.xors.embed a) _ _
    (BundleSegments.selected BundleSegments.towardTrue lower)) _ = _
  rw [BundleSegments.side_endpoint_tag,outer_tag]
  symm
  exact crossLift_survivor s a line height hc
    ⟨_,by rintro ⟨k,hk⟩; exact s.positioned.registry.disjoint a _ k _ hk⟩

/-- Each newly created inner boundary is the appropriate retained row port,
including the alternating orientation of the four mandatory arcs. -/
theorem split_inner_endpoint (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (lower : Bool) (r : Fin 4) :
    endpoint ((s.cross a line height hc).positioned.registry.bundles (.inr lower))
      (boundarySlot (!lower) r) = .inr (boundaryPort (!lower) r).val := by
  change endpoint (BundleSegments.side (s.positioned.registry.bundles _)
    (s.positioned.registry.xors.embed a) _ _
    (BundleSegments.selected BundleSegments.towardTrue lower)) _ = _
  rw [BundleSegments.side_endpoint_tag,inner_tag]
  rfl

/-- Actual registry arcs, oriented from source to target. -/
theorem boundary_edge (s : IntervalState n) (b : s.BundleId) (r : Fin 4) :
    s.adj
      (endpoint (s.positioned.registry.bundles b)
        (boundarySlot (decide (r.val % 2 ≠ 0)) r))
      (endpoint (s.positioned.registry.bundles b)
        (boundarySlot (decide (r.val % 2 = 0)) r)) := by
  have he := (s.positioned.registry.bundles b).edge r
  fin_cases r <;> exact he

end GridHardness.CorrectedSatInterval.VerticalEdges
