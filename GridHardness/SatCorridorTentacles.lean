/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCollarRunClearance
public import GridHardness.SignedTentacleCardinalSegments

/-!
# SAT Corridor Tentacles

Construct the actual width-two central tentacle of every SAT edge.
All run-length, turn and within-route clearance obligations are discharged
from the proved SAT drawing. These central pieces stop at the reserved
endpoint neighborhoods; owner docks and recipient collars remain separate.
-/

@[expose] public section

namespace GridHardness.SatCorridorTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open SatCollarCorridors
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int

noncomputable def firstRun (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteRuns.Run := (runs x hw e).head (runs_nonempty x hw e)

noncomputable def remainingRuns (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    List LatticeRouteRuns.Run := (runs x hw e).tail

theorem runs_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    firstRun x hw e::remainingRuns x hw e=runs x hw e :=
  List.cons_head_tail (runs_nonempty x hw e)

theorem firstRun_long (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    32≤(firstRun x hw e).2 := runs_long x hw e _ (List.head_mem _)

theorem remainingRuns_long (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ∀ r∈remainingRuns x hw e,32≤r.2 :=
  fun r hr => runs_long x hw e r (List.mem_of_mem_tail hr)

theorem turns (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ((firstRun x hw e).1::(remainingRuns x hw e).map Prod.fst).IsChain
      (fun d f => d.val%2≠f.val%2) := by
  change ((firstRun x hw e::remainingRuns x hw e).map Prod.fst).IsChain _
  rw [runs_eq]
  exact runs_turns x hw e

noncomputable def drawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Drawing :=
  CardinalRunChain.drawing (startPoint x hw e) (firstRun x hw e).1 (firstRun x hw e).2
    (remainingRuns x hw e)

noncomputable def terminalLane (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Fin 2 :=
  (RunChain.terminal (initialRunState (startPoint x hw e) (firstRun x hw e).1)
    (firstRun x hw e).2 (CardinalRunChain.requests
      (initialRunState (startPoint x hw e) (firstRun x hw e).1)
      (firstRun x hw e).2 (remainingRuns x hw e))).1.lane

/-- No unproved geometric premise remains in validity of the actual central piece. -/
theorem valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).Valid := by
  apply CardinalRunChain.drawing_valid_of_cardinal_clearance
  · have := firstRun_long x hw e; omega
  · intro r hr; have := remainingRuns_long x hw e r hr; omega
  · exact turns x hw e
  · change CardinalRunChain.CardinalClearance
      (LatticeRouteRuns.segments (startPoint x hw e) (firstRun x hw e::remainingRuns x hw e))
    rw [runs_eq]
    intro i j hi hj hij k hk m hm
    have hd := segment_distance x hw e i j hi hj hij k m hk hm
    exact (by decide : 6≤32).trans hd

theorem start (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).start 0=startPoint x hw e := CardinalRunChain.drawing_start _ _ _ _

/-- The actual central tip reaches the prescribed endpoint, in its tracked lane. -/
theorem tip (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).tip (terminalLane x hw e)=endPoint x hw e := by
  have h := CardinalRunChain.drawing_tip (startPoint x hw e) (firstRun x hw e).1
    (firstRun x hw e).2 (remainingRuns x hw e) (turns x hw e)
  change (LatticeRouteRuns.expandRuns (startPoint x hw e)
    (firstRun x hw e::remainingRuns x hw e)).getLast?=some ((drawing x hw e).tip _) at h
  rw [runs_eq,runs_reconstruct] at h
  exact Option.some.inj (h.symm.trans (route_certificate x hw e).2.1)

theorem stripCount (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    RunChain.stripCount (drawing x hw e)=(runs x hw e).length := by
  rw [drawing,CardinalRunChain.drawing_stripCount]
  have h := congrArg List.length (runs_eq x hw e)
  simpa only [List.length_cons] using h

/-- A polynomial geometric size bound, independent of a certified enumeration program. -/
theorem halfSize_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).halfSize≤12582912*(x.length+1) := by
  have h := CardinalRunChain.drawing_halfSize_le (startPoint x hw e) (firstRun x hw e).1
    (firstRun x hw e).2 (remainingRuns x hw e)
  have hs := runs_total_steps x hw e
  rw [← runs_eq,List.map_cons,List.sum_cons] at hs
  have hl := congrArg List.length (runs_eq x hw e)
  simp only [List.length_cons] at hl
  have hc := runs_count_bound x hw e
  have hr := (route_certificate x hw e).2.2.2.2.2
  change (drawing x hw e).halfSize≤_ at h
  omega

theorem card_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).points.card≤25165824*(x.length+1) := by
  rw [Drawing.card _ (valid x hw e)]
  have h := halfSize_le x hw e
  omega

/-- Every generated strip vertex lies within two steps of the actual corridor. -/
theorem centerline_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (p : Point) (hp : p ∈(drawing x hw e).points) :
    ∃ q∈route x hw e,IntegerGrid.manhattan p q≤2 := by
  have h := CardinalRunChain.drawing_centerline_distance (startPoint x hw e) (firstRun x hw e).1
    (firstRun x hw e).2 (remainingRuns x hw e) (turns x hw e) p hp
  change ∃ q∈LatticeRouteRuns.expandRuns (startPoint x hw e)
    (firstRun x hw e::remainingRuns x hw e),IntegerGrid.manhattan p q≤2 at h
  simpa only [runs_eq,runs_reconstruct] using h

/-- Different constructed central tentacles have no accidental contacts. -/
theorem pairwise_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hp : p ∈(drawing x hw e).points) (hq : q ∈(drawing x hw f).points) :
    28≤IntegerGrid.manhattan p q := by
  obtain ⟨u,hu,hpu⟩ := centerline_distance x hw e p hp
  obtain ⟨v,hv,hqv⟩ := centerline_distance x hw f q hq
  have hd := SatCollarCorridors.pairwise_distance x hw e f hef u v hu hv
  have h1 := IntegerGrid.manhattan_triangle u p v
  have h2 := IntegerGrid.manhattan_triangle p q v
  rw [IntegerGrid.manhattan_comm u p] at h1
  omega

theorem pairwise_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) :
    ClusterStar.Apart (drawing x hw e).points (drawing x hw f).points := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := pairwise_distance x hw e f hef p p hp hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := pairwise_distance x hw e f hef p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

/-- The central pieces remain eleven steps from all actual cluster bodies. -/
theorem cluster_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : SatNineClusterPlacement.Vertex x) (p q : Point)
    (hp : p ∈(drawing x hw e).points) (hq : q ∈SatNineClusterPlacement.points x hw v) :
    11≤IntegerGrid.manhattan p q := by
  obtain ⟨u,hu,hpu⟩ := centerline_distance x hw e p hp
  have hd := SatCollarCorridorCore.cluster_clearance x hw e v q u hq
    ((SatCollarCorridors.mem_route x hw e u).mp hu)
  have h := IntegerGrid.manhattan_triangle q p u
  rw [IntegerGrid.manhattan_comm q p] at h
  omega

theorem cluster_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : SatNineClusterPlacement.Vertex x) :
    ClusterStar.Apart (drawing x hw e).points (SatNineClusterPlacement.points x hw v) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := cluster_distance x hw e v p p hp hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := cluster_distance x hw e v p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

end GridHardness.SatCorridorTentacles
