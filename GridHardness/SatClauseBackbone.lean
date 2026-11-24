/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrder

/-!
# SAT Clause Backbone

Straight directed links from each clause exit to the next clause entry.
Their interiors lie in the vertical gaps between the reversed clause
blocks. These are the links between clauses; `SatExteriorLattice` supplies
the links to variable blocks and sentinels.
-/

@[expose] public section

namespace GridHardness.SatClauseBackbone
open CliffordSynthesis PlanarSatAssembly SatClauseOrder
set_option autoImplicit false

abbrev Point := Int × Int

def routePoint {m : Nat} (c : Fin m) (k : Nat) : Point := (-64,base c-4-k)

def route {m : Nat} (c : Fin m) : List Point :=
  (List.range 505).map (routePoint c)

def OnRoute {m : Nat} (c : Fin m) (q : Point) : Prop :=
  q.1=-64 ∧ base c-508≤q.2 ∧ q.2≤base c-4

theorem route_mem {m : Nat} (c : Fin m) (q : Point) :
    q∈route c ↔ OnRoute c q := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    dsimp [OnRoute,routePoint]
    omega
  · intro h
    refine List.mem_map.mpr ⟨(base c-4-q.2).toNat,?_,?_⟩
    · simp only [List.mem_range]
      dsimp [OnRoute] at h
      omega
    · dsimp [OnRoute] at h
      apply Prod.ext <;> dsimp [routePoint] <;> omega

theorem routePoint_injective {m : Nat} (c : Fin m) :
    Function.Injective (routePoint c) := by
  intro k l h
  have hy := congrArg Prod.snd h
  dsimp [routePoint] at hy
  omega

theorem routePoint_step {m : Nat} (c : Fin m) (k : Nat) :
    PlanarSatClause.Lattice.UnitStep (routePoint c k) (routePoint c (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  dsimp [routePoint,IntegerGrid.manhattan]
  omega

theorem route_simple {m : Nat} (c : Fin m) :
    (route c).Nodup ∧ (route c).IsChain PlanarSatClause.Lattice.UnitStep := by
  constructor
  · exact List.Nodup.map (routePoint_injective c) List.nodup_range
  · rw [route,List.isChain_map,List.isChain_range]
    intro k _
    exact routePoint_step c k

theorem route_length {m : Nat} (c : Fin m) : (route c).length=505 := by
  simp only [route,List.length_map,List.length_range]

theorem route_endpoints {m : Nat} (c d : Fin m) (hcd : d.val =c.val +1) :
    (route c).head?=some (point c 1) ∧
    (route c).getLast?=some (point d 8) := by
  have hc := (backbone_ports c).2
  have hd := (backbone_ports d).1
  rw [hc,hd,consecutive_base c d hcd]
  constructor
  · simp [route,List.head?_range,routePoint]
  · simp [route,List.getLast?_range,routePoint]
    omega

theorem endpoint_distance {m : Nat} (c d : Fin m) (hcd : d.val =c.val +1) :
    IntegerGrid.manhattan (point c 1) (point d 8)=504 := by
  rw [(backbone_ports c).2,(backbone_ports d).1,consecutive_base c d hcd]
  dsimp [IntegerGrid.manhattan]
  omega

theorem coordinates_bounded {m : Nat} (c : Fin m) (q : Point) (hq : q ∈route c) :
    q.1=-64 ∧ 0≤q.2 ∧ q.2≤3072*m+516 := by
  rw [route_mem] at hq
  have hc := c.isLt
  dsimp [OnRoute] at hq
  rw [base_eq] at hq
  omega

theorem routes_separated {m : Nat} (c e : Fin m) (hce : c ≠e) (q r : Point)
    (hq : q ∈route c) (hr : r ∈route e) : 1032≤IntegerGrid.manhattan q r := by
  rw [route_mem] at hq hr
  have hce' : c.val≠e.val := fun h => hce (Fin.ext h)
  dsimp [OnRoute] at hq hr
  rw [base_eq] at hq hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem routes_disjoint {m : Nat} (c e : Fin m) (hce : c ≠e) :
    (route c).Disjoint (route e) := by
  apply List.disjoint_left.mpr
  intro q hc he
  have hs := routes_separated c e hce q q hc he
  simp [IntegerGrid.manhattan] at hs

/-- A gap route meets the union of all clause boxes at just its two
designated endpoints, in the correct two clauses. -/
theorem box_intersection {m : Nat} (c d e : Fin m) (hcd : d.val =c.val +1)
    (q : Point) (hq : q ∈route c) (he : InBox e q) :
    (e=c ∧ q=point c 1) ∨ (e=d ∧ q=point d 8) := by
  rw [route_mem] at hq
  change q.1=-64 ∧ base c-508≤q.2 ∧ q.2≤base c-4 at hq
  change -104≤q.1 ∧ q.1≤-64 ∧ base e-4≤q.2 ∧ q.2≤base e+1028 at he
  by_cases hec : e=c
  · subst e
    left
    refine ⟨rfl,?_⟩
    rw [(backbone_ports c).2]
    apply Prod.ext <;> dsimp <;> omega
  · by_cases hed : e=d
    · subst e
      right
      refine ⟨rfl,?_⟩
      rw [(backbone_ports d).1]
      have hb := consecutive_base c d hcd
      apply Prod.ext <;> dsimp <;> omega
    · have hec' : e.val≠c.val := fun h => hec (Fin.ext h)
      have hed' : e.val≠d.val := fun h => hed (Fin.ext h)
      rw [base_eq] at hq he
      omega

theorem box_interior_clear {m : Nat} (c d e : Fin m) (hcd : d.val =c.val +1)
    (q : Point) (hq : q ∈route c) (hc : q ≠point c 1) (hd : q ≠point d 8) :
    ¬ InBox e q := by
  intro he
  rcases box_intersection c d e hcd q hq he with h | h
  · exact hc h.2
  · exact hd h.2

theorem endpoint_mem {m : Nat} (c d : Fin m) (hcd : d.val =c.val +1) :
    point c 1∈route c ∧ point d 8∈route c := by
  rw [route_mem,route_mem,(backbone_ports c).2,(backbone_ports d).1]
  rw [consecutive_base c d hcd]
  dsimp [OnRoute]
  constructor <;> omega

/-- Intersections with an internal clause edge occur precisely at an
incident backbone endpoint. This excludes unlisted crossings and overlaps. -/
theorem internal_route_intersection {m : Nat} (c d e : Fin m)
    (hcd : d.val =c.val +1) (f : Fin 14) (q : Point) :
    (q∈route c ∧ q∈SatClauseOrder.route e f) ↔
      (e=c ∧ q=point c 1 ∧
        (1=(PlanarSatClause.Lattice.edge f).1 ∨ 1=(PlanarSatClause.Lattice.edge f).2)) ∨
      (e=d ∧ q=point d 8 ∧
        (8=(PlanarSatClause.Lattice.edge f).1 ∨ 8=(PlanarSatClause.Lattice.edge f).2)) := by
  constructor
  · rintro ⟨hq,hf⟩
    have hb := SatClauseOrder.route_in_box e f q hf
    rcases box_intersection c d e hcd q hq hb with hc | hd
    · rcases hc with ⟨he,hq⟩
      subst e
      subst q
      exact Or.inl ⟨rfl,rfl,(SatClausePlacement.route_vertex_clear (Fin.rev c) f 1).mp hf⟩
    · rcases hd with ⟨he,hq⟩
      subst e
      subst q
      exact Or.inr ⟨rfl,rfl,(SatClausePlacement.route_vertex_clear (Fin.rev d) f 8).mp hf⟩
  · intro h
    rcases h with hc | hd
    · rcases hc with ⟨he,hq,hf⟩
      subst e
      subst q
      exact ⟨(endpoint_mem c d hcd).1,
        (SatClausePlacement.route_vertex_clear (Fin.rev c) f 1).mpr hf⟩
    · rcases hd with ⟨he,hq,hf⟩
      subst e
      subst q
      exact ⟨(endpoint_mem c d hcd).2,
        (SatClausePlacement.route_vertex_clear (Fin.rev d) f 8).mpr hf⟩

theorem wire_vertex_separation {n m : Nat} (φ : Formula n m) (c : Fin m)
    (q : Point) (hq : q ∈route c)
    (v : SatCrossingWireVertices.Vertex (permutation φ)) :
    64≤IntegerGrid.manhattan q (SatCrossingWireVertices.point _ v) := by
  have hw := SatCrossingWireVertices.point_bounds (permutation φ) v
  have hx := (route_mem c q).mp hq
  dsimp [OnRoute,IntegerGrid.manhattan] at hx ⊢
  omega

end GridHardness.SatClauseBackbone
