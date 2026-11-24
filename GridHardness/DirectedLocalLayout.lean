/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridGeometry
public import GridHardness.DirectedToBipartite

/-!
# Directed Local Layout

Axis-aligned rays and separated ports for the local drawings of directed vertices.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GridHardness.DirectedLocalLayout
open CliffordSynthesis

/-- Cardinal directions in clockwise order, starting east. -/
def ray (d : Fin 4) (r : Nat) : Int × Int :=
  ![((r : Int),0),(0,(r : Int)),(-(r : Int),0),(0,-(r : Int))] d

@[simp] theorem ray_zero (d : Fin 4) : ray d 0 = (0,0) := by
  fin_cases d <;> rfl

@[simp] theorem ray_eq_origin (d : Fin 4) (r : Nat) : ray d r = (0,0) ↔ r = 0 := by
  fin_cases d <;> simp [ray]

/-- Positive portions of distinct cardinal rays are disjoint. -/
theorem ray_eq_ray_iff (d e : Fin 4) {r s : Nat} (hr : 0 < r) (hs : 0 < s) :
    ray d r = ray e s ↔ d = e ∧ r = s := by
  fin_cases d <;> fin_cases e <;> simp [ray] <;> omega

/-- Distinct positive cardinal rays have no accidental unit-grid adjacencies. -/
theorem ray_adjacent_iff (d e : Fin 4) {r s : Nat} (hr : 0 < r) (hs : 0 < s) :
    IntegerGrid.manhattan (ray d r) (ray e s) = 1 ↔
      d = e ∧ (r+1 = s ∨ s+1 = r) := by
  rw [manhattan_one_iff]
  fin_cases d <;> fin_cases e <;> simp [ray] <;> omega

@[simp] theorem origin_adjacent_ray_iff (d : Fin 4) (r : Nat) :
    IntegerGrid.manhattan (0,0) (ray d r) = 1 ↔ r = 1 := by
  fin_cases d <;> simp [IntegerGrid.manhattan,ray]

/-- A finite star drawing whose arms occupy distinct cardinal rays. -/
abbrev StarVertex (ports : Finset (Fin 4)) (radius : Nat) :=
  Option ({d : Fin 4 // d ∈ ports} × Fin radius)

def starPoint {ports : Finset (Fin 4)} {radius : Nat} :
    StarVertex ports radius → Int × Int
  | none => (0,0)
  | some (d,r) => ray d.val (r.val+1)

/-- This explicitly constructed star has no coincident vertices. -/
theorem starPoint_injective (ports : Finset (Fin 4)) (radius : Nat) :
    Function.Injective (starPoint (ports := ports) (radius := radius)) := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some p =>
      have := (ray_eq_origin p.1.val (p.2.val+1)).mp h.symm
      omega
  | some p =>
    cases y with
    | none =>
      have := (ray_eq_origin p.1.val (p.2.val+1)).mp h
      omega
    | some q =>
      have he := (ray_eq_ray_iff p.1.val q.1.val (by omega) (by omega)).mp h
      congr 1
      exact Prod.ext (Subtype.ext he.1) (Fin.ext (by omega))

/-- Exact induced-grid adjacency of two noncentral star vertices. -/
theorem star_adjacent_some_iff {ports : Finset (Fin 4)} {radius : Nat}
    (d e : {d : Fin 4 // d ∈ ports}) (r s : Fin radius) :
    IntegerGrid.manhattan (starPoint (some (d,r))) (starPoint (some (e,s))) = 1 ↔
      d = e ∧ (r.val+1 = s.val ∨ s.val+1 = r.val) := by
  change IntegerGrid.manhattan (ray d.val (r.val+1)) (ray e.val (s.val+1)) = 1 ↔ _
  rw [ray_adjacent_iff d.val e.val (by omega) (by omega)]
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨Subtype.ext h,by omega⟩
  · rintro ⟨rfl,h⟩
    exact ⟨rfl,by omega⟩

/-- Only the first vertex on each arm is adjacent to the center. -/
theorem star_adjacent_center_iff {ports : Finset (Fin 4)} {radius : Nat}
    (d : {d : Fin 4 // d ∈ ports}) (r : Fin radius) :
    IntegerGrid.manhattan (starPoint (none : StarVertex ports radius))
      (starPoint (some (d,r))) = 1 ↔ r.val = 0 := by
  change IntegerGrid.manhattan (0,0) (ray d.val (r.val+1)) = 1 ↔ _
  rw [origin_adjacent_ray_iff]
  omega

/-- Coordinates stay in a square whose radius is the arm length. -/
theorem starPoint_bound {ports : Finset (Fin 4)} {radius : Nat}
    (v : StarVertex ports radius) :
    (starPoint v).1.natAbs ≤ radius ∧ (starPoint v).2.natAbs ≤ radius := by
  cases v with
  | none => simp [starPoint]
  | some p =>
    rcases p with ⟨⟨d,hd⟩,r⟩
    have hr := r.isLt
    fin_cases d <;> simp [starPoint,ray] <;> omega

/-- The singleton port carries the internal four-vertex path. If the singleton
is incoming, index zero lies at radius three; if outgoing, index three does. -/
def vertexPoint (singleton : Fin 4) (singletonIncoming : Bool) (i : Fin 4) : Int × Int :=
  ray singleton (if singletonIncoming then 3-i.val else i.val)

theorem vertexPoint_injective (d : Fin 4) (incoming : Bool) :
    Function.Injective (vertexPoint d incoming) := by
  intro i j h
  fin_cases d <;> cases incoming <;> simp [vertexPoint,ray] at h <;>
    apply Fin.ext <;> have := i.isLt <;> have := j.isLt <;> omega

/-- The four gadget positions induce exactly a path in the lattice. -/
theorem vertexPoint_adjacent_iff (d : Fin 4) (incoming : Bool) (i j : Fin 4) :
    IntegerGrid.manhattan (vertexPoint d incoming i) (vertexPoint d incoming j) = 1 ↔
      i.val+1 = j.val ∨ j.val+1 = i.val := by
  rw [manhattan_one_iff]
  fin_cases d <;> cases incoming <;> simp [vertexPoint,ray] <;>
    have := i.isLt <;> have := j.isLt <;> omega

/-- The two remaining port wires cannot intersect an interior gadget vertex. -/
theorem other_port_disjoint (d e : Fin 4) (hde : d ≠ e) (incoming : Bool)
    (i : Fin 4) {r : Nat} (hr : 0 < r) : vertexPoint d incoming i ≠ ray e r := by
  intro h
  dsimp [vertexPoint] at h
  by_cases hz : (if incoming then 3-i.val else i.val) = 0
  · rw [hz,ray_zero] at h
    have := (ray_eq_origin e r).mp h.symm
    omega
  · exact hde ((ray_eq_ray_iff d e (by omega) hr).mp h).1

/-- The nonsingleton port wires attach only at their intended branch vertex. -/
theorem other_port_adjacent_iff (d e : Fin 4) (hde : d ≠ e) (incoming : Bool)
    (i : Fin 4) {r : Nat} (hr : 0 < r) :
    IntegerGrid.manhattan (vertexPoint d incoming i) (ray e r) = 1 ↔
      (if incoming then i = 3 else i = 0) ∧ r = 1 := by
  rw [manhattan_one_iff]
  have hi := i.isLt
  fin_cases d <;> fin_cases e <;> cases incoming <;> fin_cases i <;>
    simp_all [vertexPoint,ray] <;> omega

/-- The singleton wire starts beyond radius three and misses all gadget vertices. -/
theorem singleton_port_disjoint (d : Fin 4) (incoming : Bool)
    (i : Fin 4) {r : Nat} (hr : 3 < r) : vertexPoint d incoming i ≠ ray d r := by
  have hi := i.isLt
  fin_cases d <;> cases incoming <;> simp [vertexPoint,ray] <;> omega

/-- The singleton wire attaches precisely to the outer endpoint of the four-path. -/
theorem singleton_port_adjacent_iff (d : Fin 4) (incoming : Bool)
    (i : Fin 4) {r : Nat} (hr : 3 < r) :
    IntegerGrid.manhattan (vertexPoint d incoming i) (ray d r) = 1 ↔
      (if incoming then i = 0 else i = 3) ∧ r = 4 := by
  rw [manhattan_one_iff]
  have hi := i.isLt
  fin_cases d <;> cases incoming <;> fin_cases i <;>
    simp_all [vertexPoint,ray] <;> omega

end GridHardness.DirectedLocalLayout
