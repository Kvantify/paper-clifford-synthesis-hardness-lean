/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCollarCorridors
public import GridHardness.LatticeRouteRunSegments

/-!
# SAT Collar Run Clearance

The remaining nonconsecutive-run clearance is proved for the actual
SAT corridors. It follows from original route simplicity and the sixty-four
fold dilation, not from an additional geometric certificate.
-/

@[expose] public section

namespace GridHardness.SatCollarCorridors
open CliffordComplexity CliffordSynthesis LatticeRouteRuns
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem indexSeparated (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteCore.IndexSeparated 64 (route x hw e) := by
  apply LatticeRouteCore.indexSeparated_orient
  have h := SatBipartiteDrawing.route_certificate x hw e
  exact LatticeRouteCore.core_indexSeparated 64 16 16 (by decide) _
    h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

/-- Positioned ideal segments obtained by expanding the computed runs. -/
noncomputable def runSegments (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) : List Segment := segments (startPoint x hw e) (runs x hw e)

theorem runSegments_length (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (runSegments x hw e).length=(runs x hw e).length := segments_length _ _

/-- Nonconsecutive straight segments of each actual corridor have a
thirty-two-step margin, sufficient for the width-two strip compiler. -/
theorem segment_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (i j : Nat) (hi : i <(runSegments x hw e).length) (hj : j <(runSegments x hw e).length)
    (hij : i +1<j) (k m : Nat)
    (hk : k ≤((runSegments x hw e)[i]'hi).2.2)
    (hm : m ≤((runSegments x hw e)[j]'hj).2.2) :
    32≤IntegerGrid.manhattan
      (segmentPoint ((runSegments x hw e)[i]'hi) k)
      (segmentPoint ((runSegments x hw e)[j]'hj) m) := by
  have hs : LatticeRouteCore.IndexSeparated 64
      (expandRuns (startPoint x hw e) (runs x hw e)) := by
    rw [runs_reconstruct]
    exact indexSeparated x hw e
  exact segments_index_distance 64 32 (startPoint x hw e) (runs x hw e) hs
    (runs_long x hw e) i j hi hj hij k m hk hm

/-- Every ideal segment point is a point of the exact owner-oriented
corridor, including both closed segment endpoints. -/
theorem segmentPoint_mem_route (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (a : Segment) (ha : a ∈runSegments x hw e) (k : Nat) (hk : k ≤a.2.2) :
    segmentPoint a k∈route x hw e := by
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  have hi' : i<(runs x hw e).length := by simpa only [runSegments_length] using hi
  have hh : ((runSegments x hw e)[i]'hi).2=(runs x hw e)[i]'hi' :=
    segments_getElem_run (startPoint x hw e) (runs x hw e) i hi'
  have hk' : k≤((runs x hw e)[i]'hi').2 := by
    rw [← hh]
    exact hk
  have he := segmentPoint_getElem (startPoint x hw e) (runs x hw e) i k hi' hk'
  have hmem : segmentPoint ((runSegments x hw e)[i]'hi) k∈
      expandRuns (startPoint x hw e) (runs x hw e) := by
    change segmentPoint ((segments (startPoint x hw e) (runs x hw e))[i]) k∈_
    rw [he]
    exact List.getElem_mem _
  simpa only [runs_reconstruct] using hmem

end GridHardness.SatCollarCorridors
