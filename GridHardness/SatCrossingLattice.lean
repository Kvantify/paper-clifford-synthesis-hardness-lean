/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PermutationWireLayout
public import GridHardness.XorLineLattice
public import GridHardness.SignedTentacleFrame

/-!
# SAT Crossing Lattice

Place the actual crossing gadgets at the permutation's crossing
coordinates. The boxes and their internal routes are disjoint and linearly
bounded. This is a component of the drawing, not a theorem about inter-box
wires or the complete SAT graph.
-/

@[expose] public section

namespace GridHardness.SatCrossingLattice
open CliffordSynthesis SignedTentacle PermutationWireLayout
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))
abbrev Cell (n : Nat) := Fin n × Fin n

/-- The main true ports face right and the false ports left. Row ports face
up/down; reversing their direction does not change the occupied box. -/
def frame (c : Cell n) : Frame :=
  ⟨false, false, true, (512*low c.1+65, 512*high p c.2-10)⟩

theorem frame_map (c : Cell n) (q : Int × Int) :
    (frame p c).map q = (512*low c.1+65-q.2, 512*high p c.2-10+q.1) := by
  simp [frame, Frame.map, OrthogonalTentacle.place, sign]
  omega

def point (c : Cell n) (v : XorLine.Vertex 4) : Int × Int :=
  (frame p c).map (XorLine.Lattice.point v)

def route (c : Cell n) (i : Fin 66) : List (Int × Int) :=
  (XorLine.Lattice.edgeRoute i).map (frame p c).map

def InBox (c : Cell n) (q : Int × Int) : Prop :=
  512*low c.1-65 ≤ q.1 ∧ q.1 ≤ 512*low c.1+65 ∧
    512*high p c.2-10 ≤ q.2 ∧ q.2 ≤ 512*high p c.2+10

theorem map_in_box (c : Cell n) (q : Int × Int) (hq : XorLine.Lattice.InBox q) :
    InBox p c ((frame p c).map q) := by
  rw [frame_map]
  change 0 ≤ q.1 ∧ q.1 ≤ 20 ∧ 0 ≤ q.2 ∧ q.2 ≤ 130 at hq
  dsimp [InBox]
  omega

private theorem local_point_in_box : ∀ v : XorLine.Vertex 4,
    XorLine.Lattice.InBox (XorLine.Lattice.point v) := by decide +kernel

theorem point_in_box (c : Cell n) (v : XorLine.Vertex 4) : InBox p c (point p c v) :=
  map_in_box p c _ (local_point_in_box v)

theorem route_in_box (c : Cell n) (i : Fin 66) (q : Int × Int) (hq : q ∈ route p c i) :
    InBox p c q := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact map_in_box p c r ((XorLine.Lattice.route_certificate i).2.2.2.2.2.2 r hr)

/-- Even points on different box boundaries are separated by hundreds of
unit steps. In particular, different gadgets introduce no unintended edges. -/
theorem boxes_separated (c d : Cell n) (hcd : c ≠ d) (q r : Int × Int)
    (hq : InBox p c q) (hr : InBox p d r) : 382 ≤ IntegerGrid.manhattan q r := by
  by_cases hx : c.1=d.1
  · have hy : c.2 ≠ d.2 := fun he => hcd (Prod.ext hx he)
    have hh : high p c.2 ≠ high p d.2 := fun he => hy (high_injective p he)
    dsimp [InBox, IntegerGrid.manhattan] at hq hr ⊢
    omega
  · have hh : low c.1 ≠ low d.1 := fun he => hx (low_injective he)
    dsimp [InBox, IntegerGrid.manhattan] at hq hr ⊢
    omega

theorem point_injective : Function.Injective (fun cv : Cell n × XorLine.Vertex 4 =>
    point p cv.1 cv.2) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ he
  change point p c v = point p d w at he
  by_cases hc : c=d
  · subst d
    exact Prod.ext rfl (XorLine.Lattice.point_injective ((frame p c).injective he))
  · have hh := boxes_separated p c d hc _ _ (point_in_box p c v) (point_in_box p d w)
    rw [he] at hh
    simp [IntegerGrid.manhattan] at hh

theorem coordinates_bounded (c : Cell n) (q : Int × Int) (hq : InBox p c q) :
    0 ≤ q.1 ∧ q.1 ≤ 512*n+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*n+522 := by
  have hl := low_bounds c.1
  have hh := high_bounds p c.2
  dsimp [InBox] at hq
  omega

theorem route_certificate (c : Cell n) (i : Fin 66) :
    (route p c i).head? = some (point p c (XorLine.Lattice.edge i).1) ∧
    (route p c i).getLast? = some (point p c (XorLine.Lattice.edge i).2) ∧
    (route p c i).Nodup ∧ (route p c i).IsChain XorLine.Lattice.UnitStep ∧
    2 ≤ (route p c i).length ∧ (route p c i).length ≤ 17 := by
  obtain ⟨hh, ht, hn, hs, hl, hu, _⟩ := XorLine.Lattice.route_certificate i
  refine ⟨?_, ?_, hn.map (frame p c).injective, ?_, ?_, ?_⟩
  · simp only [route, List.head?_map, hh, Option.map_some, point]
  · simp only [route, List.getLast?_map, ht, Option.map_some, point]
  · apply List.isChain_map_of_isChain (frame p c).map _ hs
    intro a b hab
    change IntegerGrid.manhattan _ _ = 1
    rw [(frame p c).distance]
    exact hab
  · simpa only [route, List.length_map] using hl
  · simpa only [route, List.length_map] using hu

theorem distinct_cell_routes_disjoint (c d : Cell n) (hcd : c ≠ d) (i j : Fin 66) :
    (route p c i).Disjoint (route p d j) := by
  apply List.disjoint_left.mpr
  intro q hq hr
  have hh := boxes_separated p c d hcd q q (route_in_box p c i q hq) (route_in_box p d j q hr)
  simp [IntegerGrid.manhattan] at hh

theorem route_vertex_clear (c : Cell n) (i : Fin 66) (v : XorLine.Vertex 4) :
    point p c v ∈ route p c i ↔ v = (XorLine.Lattice.edge i).1 ∨
      v = (XorLine.Lattice.edge i).2 := by
  change (frame p c).map (XorLine.Lattice.point v) ∈
    (XorLine.Lattice.edgeRoute i).map (frame p c).map ↔ _
  rw [List.mem_map_of_injective (frame p c).injective]
  exact XorLine.Lattice.route_vertex_clear i v

/-- The two main pairs lie on the horizontal boundary; the orientation
retains each input/output pair on its own side. -/
theorem main_port_coordinates (c : Cell n) :
    point p c (XorLine.inputPort 4 (.inl true)) =
      (512*low c.1+65, 512*high p c.2-4) ∧
    point p c (XorLine.outputPort 4 (.inl true)) =
      (512*low c.1+65, 512*high p c.2+4) ∧
    point p c (XorLine.inputPort 4 (.inl false)) =
      (512*low c.1-65, 512*high p c.2+4) ∧
    point p c (XorLine.outputPort 4 (.inl false)) =
      (512*low c.1-65, 512*high p c.2-4) := by
  obtain ⟨a,b,c',d⟩ := XorLine.Lattice.main_port_coordinates
  unfold point
  rw [a, b, c', d, frame_map, frame_map, frame_map, frame_map]
  simp only [Prod.mk.injEq]
  omega

end GridHardness.SatCrossingLattice
