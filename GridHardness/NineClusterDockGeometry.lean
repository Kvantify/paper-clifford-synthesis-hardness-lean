/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.ClusterStar
public import GridHardness.DirectedLocalLayout

/-!
# Nine Cluster Dock Geometry

Separation and cardinal geometry of the concrete nine-cluster docks.
All four outward directions are available for either one-edge or two-edge
attachment. These local facts apply to arbitrary straight stub lengths;
construction of bends and the full inter-cluster collars is separate.
-/

@[expose] public section

namespace GridHardness.NineClusterDockGeometry
open CliffordSynthesis OrthogonalTentacle SignedTentacle NineClusterAttachment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Cardinal directions use east, north, west, south, whereas the cluster
sides are numbered left, bottom, right, top. -/
def sideOfDirection (d : Fin 4) : Fin 4 := ⟨(d.val+2)%4,Nat.mod_lt _ (by decide)⟩

def directionOfSide (s : Fin 4) : Fin 4 := ⟨(s.val+2)%4,Nat.mod_lt _ (by decide)⟩

@[simp] theorem direction_side (d : Fin 4) : directionOfSide (sideOfDirection d)=d := by
  fin_cases d <;> decide

@[simp] theorem side_direction (s : Fin 4) : sideOfDirection (directionOfSide s)=s := by
  fin_cases s <;> decide

theorem sideOfDirection_injective : Function.Injective sideOfDirection :=
  Function.LeftInverse.injective direction_side

theorem directionOfSide_injective : Function.Injective directionOfSide :=
  Function.LeftInverse.injective side_direction

/-- Longitudinal motion in a docking frame follows the corresponding
cardinal ray, for both lanes and both attachment parities. -/
theorem dock_ray (b : Bool) (s : Fin 4) (r : Fin 2) (k : Nat) :
    (dock b s).map ((k:Int),(r.val:Int))=
      ((near (dock b s) r).1+(DirectedLocalLayout.ray (directionOfSide s) k).1,
       (near (dock b s) r).2+(DirectedLocalLayout.ray (directionOfSide s) k).2) := by
  fin_cases s <;> cases b <;>
    simp [dock,near,Frame.map,place,sign,directionOfSide,DirectedLocalLayout.ray]

theorem far_ray (b : Bool) (s : Fin 4) (r : Fin 2) (n : Nat) :
    far (dock b s) n r=
      ((near (dock b s) r).1+(DirectedLocalLayout.ray (directionOfSide s) n).1,
       (near (dock b s) r).2+(DirectedLocalLayout.ray (directionOfSide s) n).2) :=
  dock_ray b s r n

/-- Docks on distinct sides have no common vertices and no unintended
unit adjacency, even when their one-edge/two-edge choices differ. -/
theorem dock_distance (b c : Bool) (s t : Fin 4) (hst : s ≠t)
    (n m : Nat) (p q : Point) (hp : p ∈strip (dock b s) n)
    (hq : q ∈strip (dock c t) m) : 2≤IntegerGrid.manhattan p q := by
  have hp := (mem_strip_iff (dock b s) n p).mp hp
  have hq := (mem_strip_iff (dock c t) m q).mp hq
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  fin_cases s <;> fin_cases t
  all_goals first
    | exact False.elim (hst rfl)
    | cases b <;> cases c <;>
        simp [dock,Frame.unmap,sign] at hp hq <;>
        dsimp [IntegerGrid.manhattan] <;> omega

theorem docks_apart (b c : Bool) (s t : Fin 4) (hst : s ≠t) (n m : Nat) :
    ClusterStar.Apart (strip (dock b s) n) (strip (dock c t) m) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := dock_distance b c s t hst n m p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := dock_distance b c s t hst n m p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

/-- The same separation holds after a common signed placement frame. -/
theorem frame_dock_distance (f : Frame) (b c : Bool) (s t : Fin 4) (hst : s ≠t)
    (n m : Nat) (p q : Point) (hp : p ∈(strip (dock b s) n).image f.map)
    (hq : q ∈(strip (dock c t) m).image f.map) : 2≤IntegerGrid.manhattan p q := by
  obtain ⟨p,hp0,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q,hq0,rfl⟩ := Finset.mem_image.mp hq
  rw [f.distance]
  exact dock_distance b c s t hst n m p q hp0 hq0

theorem frame_docks_apart (f : Frame) (b c : Bool) (s t : Fin 4)
    (hst : s ≠t) (n m : Nat) :
    ClusterStar.Apart ((strip (dock b s) n).image f.map)
      ((strip (dock c t) m).image f.map) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := frame_dock_distance f b c s t hst n m p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := frame_dock_distance f b c s t hst n m p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

/-- Signed coordinate along a cardinal direction, relative to the
cluster center `(1,1)`. -/
def radial (d : Fin 4) (p : Point) : Int :=
  ![p.1-1,p.2-1,1-p.1,1-p.2] d

/-- The transverse coordinate uses the counterclockwise perpendicular. -/
def transverse (d : Fin 4) (p : Point) : Int :=
  ![p.2-1,1-p.1,1-p.2,p.1-1] d

/-- A dock strip stays at radial distance two or more and within two
units of its cardinal axis. -/
theorem radial_bounds (b : Bool) (s : Fin 4) (n : Nat) (p : Point)
    (hp : p ∈strip (dock b s) n) :
    2≤radial (directionOfSide s) p ∧ radial (directionOfSide s) p≤(n:Int)+2 ∧
      -2≤transverse (directionOfSide s) p ∧ transverse (directionOfSide s) p≤2 := by
  have hp := (mem_strip_iff (dock b s) n p).mp hp
  rcases p with ⟨x,y⟩
  fin_cases s <;> cases b <;>
    simp [dock,Frame.unmap,sign,radial,transverse,directionOfSide] at hp ⊢ <;> omega

/-- All local dock vertices lie in a square whose radius grows only
with the stub length. -/
theorem point_bounds (b : Bool) (s : Fin 4) (n : Nat) (p : Point)
    (hp : p ∈strip (dock b s) n) :
    -(n:Int)-1≤p.1 ∧ p.1≤(n:Int)+3 ∧ -(n:Int)-1≤p.2 ∧ p.2≤(n:Int)+3 := by
  have hp := (mem_strip_iff (dock b s) n p).mp hp
  rcases p with ⟨x,y⟩
  fin_cases s <;> cases b <;>
    simp [dock,Frame.unmap,sign] at hp <;> dsimp <;> omega

/-- Exact distance from the cluster center to each longitudinal lane
position. The outer lane of a one-edge dock is two units off its axis. -/
theorem center_distance (b : Bool) (s : Fin 4) (r : Fin 2) (k : Nat) :
    IntegerGrid.manhattan (1,1) ((dock b s).map ((k:Int),(r.val:Int)))=
      k+2+(if r=0 then 1 else if b then 0 else 2) := by
  fin_cases s <;> cases b <;> fin_cases r <;>
    simp [dock,Frame.map,place,sign,IntegerGrid.manhattan] <;> omega

theorem center_distance_bounds (b : Bool) (s : Fin 4) (n : Nat) (p : Point)
    (hp : p ∈strip (dock b s) n) :
    2≤IntegerGrid.manhattan (1,1) p ∧ IntegerGrid.manhattan (1,1) p≤n+4 := by
  have hp := (mem_strip_iff (dock b s) n p).mp hp
  rcases p with ⟨x,y⟩
  fin_cases s <;> cases b <;>
    simp [dock,Frame.unmap,sign] at hp <;>
    dsimp [IntegerGrid.manhattan] <;> omega

end GridHardness.NineClusterDockGeometry
