/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.NineClusterOwnerRun
public import GridHardness.SignedTentacleRunDirections
public import GridHardness.SatDockCorridors

/-!
# SAT Owner Tentacles

Actual signed tentacles beginning at the owner cluster's prescribed
two-edge dock. Their centerlines are the computed asymmetric SAT routes,
and every initial and terminal frame is derived from those routes.
-/

@[expose] public section

namespace GridHardness.SatOwnerTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open SignedTentacle.CardinalRunChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Edge := SatDockCorridors.Edge

noncomputable def state (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : RunState :=
  NineClusterOwnerRun.state (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
    (SatDockCorridors.side x hw e false)

noncomputable def firstRun (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Run :=
  (SatDockCorridors.runs x hw e).head (SatDockCorridors.runs_nonempty x hw e)

noncomputable def remaining (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : List Run :=
  (SatDockCorridors.runs x hw e).tail

noncomputable def drawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Drawing :=
  drawingFrom (state x hw e) (firstRun x hw e).2 (remaining x hw e)

noncomputable def terminalState (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : RunState :=
  (RunChain.terminal (state x hw e) (firstRun x hw e).2
    (requests (state x hw e) (firstRun x hw e).2 (remaining x hw e))).1

@[simp] theorem state_length (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (n : Nat) : (state x hw e).length n = n :=
  NineClusterOwnerRun.state_length _ _ _

theorem owner_color (x : SatTy.denote) (e : Edge x) :
    SatNineClusterPlacement.color x (SatDockCorridors.owner x e) = 0 := by
  have h := (SatCollarCorridors.owners x e).1
  change decide (SatNineClusterPlacement.color x (SatDockCorridors.owner x e) = 0) = true at h
  exact of_decide_eq_true h

theorem state_direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (state x hw e).frame.axisDirection = SatDockCorridors.direction x hw e false := by
  unfold state SatNineClusterPlacement.frame
  rw [NineClusterOwnerRun.state_direction]
  exact NineClusterDockGeometry.direction_side _

theorem state_point (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (state x hw e).point 0 = SatDockCorridors.startPoint x hw e := by
  unfold state SatNineClusterPlacement.frame
  rw [owner_color, NineClusterOwnerRun.state_owner_start]
  simp only [SatDockCorridors.side, NineClusterDockGeometry.direction_side]
  rfl

theorem firstRun_direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (firstRun x hw e).1 = SatDockCorridors.direction x hw e false := by
  have h := LatticeRouteRuns.compress_initial_direction (SatDockCorridors.route x hw e)
    (by have := (SatDockCorridors.route_certificate x hw e).2.2.2.2.1; omega)
  rw [SatDockCorridors.route_direction] at h
  change ((SatDockCorridors.runs x hw e).map Prod.fst).head? = _ at h
  rw [← List.cons_head_tail (SatDockCorridors.runs_nonempty x hw e)] at h
  exact Option.some.inj h

theorem runs_decompose (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    SatDockCorridors.runs x hw e =
      ((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e := by
  have h := (List.cons_head_tail (SatDockCorridors.runs_nonempty x hw e)).symm
  change SatDockCorridors.runs x hw e = firstRun x hw e::remaining x hw e at h
  rw [h]
  congr 1
  exact Prod.ext ((firstRun_direction x hw e).trans (state_direction x hw e).symm) rfl

theorem directions (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ((state x hw e).frame.axisDirection::(remaining x hw e).map Prod.fst).IsChain
      (fun d f => d.val % 2 ≠ f.val % 2) := by
  have h := SatDockCorridors.runs_turns x hw e
  rw [runs_decompose] at h
  exact h

theorem lengths (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    ∀ r ∈ ((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e,
      52 ≤ r.2 := by
  rw [← runs_decompose]
  exact SatDockCorridors.runs_long x hw e

theorem expanded (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteRuns.expandRuns ((state x hw e).point 0)
      (((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e) =
        SatDockCorridors.route x hw e := by
  rw [← runs_decompose, state_point]
  exact SatDockCorridors.runs_reconstruct x hw e

theorem indexSeparated (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    LatticeRouteCore.IndexSeparated 64 (LatticeRouteRuns.expandRuns ((state x hw e).point 0)
      (((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e)) := by
  rw [expanded]
  exact SatDockCorridors.indexSeparated x hw e

theorem valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).Valid := by
  apply drawingFrom_valid
  · have h := lengths x hw e _ (List.mem_cons_self)
    omega
  · intro r hr
    have h := lengths x hw e r (List.mem_cons_of_mem _ hr)
    omega
  · exact directions x hw e
  · intro i j hi hj hij k hk l hl
    have h := LatticeRouteRuns.segments_index_distance 64 52 ((state x hw e).point 0)
      (((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e)
      (indexSeparated x hw e) (lengths x hw e) i j hi hj hij k l hk hl
    norm_num at h
    omega

theorem start (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (r : Fin 2) :
    (drawing x hw e).start r =
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map
        (near (NineClusterAttachment.dock true (SatDockCorridors.side x hw e false)) r) :=
  NineClusterOwnerRun.drawing_start _ _ _ _ _

theorem tip (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).tip (terminalState x hw e).lane = SatDockCorridors.endPoint x hw e := by
  have h := drawingFrom_tip (state x hw e) (firstRun x hw e).2 (remaining x hw e) (directions x hw e)
  rw [expanded, (SatDockCorridors.route_certificate x hw e).2.1] at h
  exact (Option.some.inj h).symm

theorem endframe_direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).lastFrame.axisDirection = SatDockCorridors.side x hw e true := by
  have h := drawingFrom_last_direction (state x hw e) (firstRun x hw e).2
    (remaining x hw e) (directions x hw e)
  have ht := LatticeRouteRuns.compress_terminal_direction (SatDockCorridors.route x hw e)
    (by have := (SatDockCorridors.route_certificate x hw e).2.2.2.2.1; omega)
    (SatDockCorridors.route_certificate x hw e).2.2.2.1
  rw [SatDockCorridors.route_direction] at ht
  change ((SatDockCorridors.runs x hw e).map Prod.fst).getLast? = _ at ht
  rw [runs_decompose] at ht
  exact (Option.some.inj (h.symm.trans ht))

theorem centerline_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (q : Point) (hq : q ∈ (drawing x hw e).points) :
    ∃ r ∈ SatDockCorridors.route x hw e, IntegerGrid.manhattan q r ≤ 2 := by
  have h := drawingFrom_centerline_distance (state x hw e) (firstRun x hw e).2
    (remaining x hw e) (directions x hw e) q hq
  rwa [expanded] at h

set_option maxHeartbeats 800000 in
-- The geometric proof unfolds the coordinates of the constructed routes.
theorem first_strip_of_close (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (q : Point) (hq : q ∈ (drawing x hw e).points)
    (hclose : IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (SatDockCorridors.owner x e)) q ≤ 7) :
    q ∈ strip (state x hw e).frame (firstRun x hw e).2 := by
  have hstart := SatDockCorridors.start_distance x hw e
  have htri := IntegerGrid.manhattan_triangle (SatDockCorridors.startPoint x hw e)
    (SatNineClusterPlacement.anchor x hw (SatDockCorridors.owner x e)) q
  rw [IntegerGrid.manhattan_comm (SatDockCorridors.startPoint x hw e)
    (SatNineClusterPlacement.anchor x hw (SatDockCorridors.owner x e))] at htri
  have h := compile_first_strip_of_close (state x hw e) (firstRun x hw e).2 (remaining x hw e)
    64 52 (directions x hw e) (indexSeparated x hw e) (lengths x hw e) q hq
    (by rw [state_point]; norm_num; omega)
  simpa only [state_length] using h

set_option maxHeartbeats 800000 in
-- The geometric proof unfolds the coordinates of the constructed routes.
theorem last_strip_of_close (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (q : Point) (hq : q ∈ (drawing x hw e).points)
    (hclose : IntegerGrid.manhattan q (SatDockCorridors.endPoint x hw e) + 2 < 52) :
    q ∈ strip (drawing x hw e).lastFrame (drawing x hw e).lastLength := by
  have he : LatticeRouteRuns.runEnd ((state x hw e).point 0)
      (((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e) =
        SatDockCorridors.endPoint x hw e := by
    have hh := LatticeRouteRuns.expandRuns_getLast ((state x hw e).point 0)
      (((state x hw e).frame.axisDirection, (firstRun x hw e).2)::remaining x hw e)
    rw [expanded, (SatDockCorridors.route_certificate x hw e).2.1] at hh
    exact (Option.some.inj hh).symm
  apply compile_last_strip_of_close (state x hw e) (firstRun x hw e).2 (remaining x hw e)
    64 52 (directions x hw e) (indexSeparated x hw e) (lengths x hw e) q hq
  simpa only [he, min_eq_right (by decide : 52 ≤ 64)] using hclose

theorem owner_interface (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    Disjoint (SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e)) (drawing x hw e).points ∧
    TwoClusterAssembly.boundary (SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e))
      (drawing x hw e).points =
        {(SatNineClusterPlacement.corner x hw (SatDockCorridors.owner x e) (SatDockCorridors.side x hw e false),
          (drawing x hw e).start 0),
         (TwoClusterAssembly.mate (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
          (SatDockCorridors.side x hw e false), (drawing x hw e).start 1)} :=
  NineClusterOwnerRun.drawing_owner_interface _ _ _ _ 64 52 (by decide)
    (directions x hw e) (indexSeparated x hw e) (lengths x hw e)

theorem stripCount (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    RunChain.stripCount (drawing x hw e) = (SatDockCorridors.runs x hw e).length := by
  rw [drawing, drawingFrom_stripCount, runs_decompose, List.length_cons]

theorem stripCount_bound (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    RunChain.stripCount (drawing x hw e) ≤ 6291456 * (x.length + 1) := by
  rw [stripCount]
  have h := LatticeRouteRuns.run_count_le (SatDockCorridors.route x hw e)
  have hb := (SatDockCorridors.route_certificate x hw e).2.2.2.2.2
  change (SatDockCorridors.runs x hw e).length ≤ _ at h
  omega

theorem halfSize_bound (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).halfSize ≤ 12582912 * (x.length + 1) := by
  have h := drawingFrom_halfSize_le (state x hw e) (firstRun x hw e).2 (remaining x hw e)
  have hs := LatticeRouteRuns.run_step_count (SatDockCorridors.route x hw e)
  have hc := LatticeRouteRuns.run_count_le (SatDockCorridors.route x hw e)
  change ((SatDockCorridors.runs x hw e).map Prod.snd).sum = _ at hs
  change (SatDockCorridors.runs x hw e).length ≤ _ at hc
  rw [runs_decompose, List.map_cons, List.sum_cons] at hs
  rw [runs_decompose, List.length_cons] at hc
  have hb := (SatDockCorridors.route_certificate x hw e).2.2.2.2.2
  change (drawing x hw e).halfSize ≤ _ at h
  omega

end GridHardness.SatOwnerTentacles
