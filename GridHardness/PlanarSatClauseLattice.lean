/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatAssembly
public import GridHardness.CrossoverLattice

/-!
# Planar SAT Clause Lattice

A lattice drawing of the fourteen internal clause edges. Literal ports
are spaced by 512, matching the occurrence-wire rows. The three omitted
right edges are supplied by the occurrence wires, not drawn through the
body. `SatClauseBackbone` draws the links between clauses.
-/

@[expose] public section

namespace GridHardness.PlanarSatClause.Lattice
open CliffordSynthesis
set_option autoImplicit false
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev Point := Int × Int
abbrev UnitStep := PlanarSatCrossover.Lattice.UnitStep

/-- Bottom, top, upper-left, lower-left in each of three literal slots. -/
def point : Fin 12 → Point :=
  ![(0,4),(0,-4),(-20,-4),(-20,4),
    (0,516),(0,508),(-20,508),(-20,516),
    (0,1028),(0,1020),(-20,1020),(-20,1028)]

def edge : Fin 14 → Fin 12 × Fin 12 :=
  ![(0,3),(2,1),(2,3),(3,6),(4,7),(5,0),(6,5),
    (6,7),(7,10),(8,11),(9,4),(10,9),(10,11),(11,2)]

def length : Fin 14 → Nat := ![20,20,8,504,20,504,20,8,504,20,504,20,8,1072]

def direction : Fin 14 → Point :=
  ![(-1,0),(1,0),(0,1),(0,1),(-1,0),(0,-1),(1,0),
    (0,1),(0,1),(-1,0),(0,-1),(1,0),(0,1),(0,0)]

/-- All edges are straight except the leftmost return from slot two to
slot zero. Its three pieces are west, south, and east. -/
def routePoint (e : Fin 14) (k : Nat) : Point :=
  if e.val=13 then
    if k≤20 then (-20-(k:Int),1028)
    else if k≤1052 then (-40,1048-(k:Int))
    else ((k:Int)-1092,-4)
  else
    ((point (edge e).1).1+(direction e).1*k,
      (point (edge e).1).2+(direction e).2*k)

def route (e : Fin 14) : List Point :=
  (List.range (length e+1)).map (routePoint e)

def InBox (q : Point) : Prop := -40≤q.1 ∧ q.1≤0 ∧ -4≤q.2 ∧ q.2≤1028
instance (q : Point) : Decidable (InBox q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Closed-coordinate description, used instead of enumerating long paths
in the separation proofs. -/
def OnRoute (e : Fin 14) (q : Point) : Prop :=
  if e.val=13 then
    (q.2=1028 ∧ -40≤q.1 ∧ q.1≤-20) ∨
    (q.1=-40 ∧ -4≤q.2 ∧ q.2≤1028) ∨
    (q.2=-4 ∧ -40≤q.1 ∧ q.1≤-20)
  else
    min (point (edge e).1).1 (point (edge e).2).1≤q.1 ∧
    q.1≤max (point (edge e).1).1 (point (edge e).2).1 ∧
    min (point (edge e).1).2 (point (edge e).2).2≤q.2 ∧
    q.2≤max (point (edge e).1).2 (point (edge e).2).2

instance (e : Fin 14) (q : Point) : Decidable (OnRoute e q) := by
  unfold OnRoute
  infer_instance

theorem point_injective : Function.Injective point := by decide +kernel
theorem edge_injective : Function.Injective edge := by decide +kernel

theorem edge_body : ∀ e : Fin 14, edge e∈PlanarSatAssembly.clauseBody := by decide +kernel

theorem body_iff_edge : ∀ u v : Fin 12,
    (u,v)∈PlanarSatAssembly.clauseBody ↔ ∃ e : Fin 14, edge e=(u,v) := by decide +kernel

theorem routePoint_injective (e : Fin 14) : Function.Injective (routePoint e) := by
  intro k l h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases e <;> dsimp [routePoint,edge,point,direction] at hx hy
  all_goals (try split_ifs at hx hy) <;> (try dsimp at hx hy) <;> omega

theorem routePoint_step (e : Fin 14) (k : Nat) :
    UnitStep (routePoint e k) (routePoint e (k+1)) := by
  change IntegerGrid.manhattan _ _=1
  fin_cases e <;> dsimp [routePoint,edge,point,direction,IntegerGrid.manhattan]
  all_goals (try split_ifs) <;> (try dsimp) <;> omega

theorem route_simple (e : Fin 14) :
    (route e).Nodup ∧ (route e).IsChain UnitStep := by
  constructor
  · exact List.Nodup.map (routePoint_injective e) List.nodup_range
  · rw [route,List.isChain_map,List.isChain_range]
    intro k _
    exact routePoint_step e k

private theorem routePoint_first : ∀ e, routePoint e 0=point (edge e).1 := by decide +kernel
private theorem routePoint_last : ∀ e, routePoint e (length e)=point (edge e).2 := by decide +kernel

theorem route_endpoints (e : Fin 14) :
    (route e).head?=some (point (edge e).1) ∧
    (route e).getLast?=some (point (edge e).2) := by
  constructor
  · simp [route,List.range_succ_eq_map,routePoint_first]
  · simp [route,List.range_succ,routePoint_last]

theorem route_length (e : Fin 14) : (route e).length=length e+1 := by simp [route]

theorem route_length_bound (e : Fin 14) : 2≤(route e).length ∧ (route e).length≤1073 := by
  rw [route_length]
  revert e
  decide +kernel

theorem route_mem (e : Fin 14) (q : Point) : q∈route e ↔ OnRoute e q := by
  constructor
  · intro h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hk
    fin_cases e <;> dsimp [length,routePoint,OnRoute,edge,point,direction] at hk ⊢
    all_goals (try split_ifs) <;> (try dsimp) <;> omega
  · intro h
    apply List.mem_map.mpr
    by_cases he : e.val=13
    · have he' : e=13 := Fin.ext he
      subst e
      norm_num [OnRoute] at h
      rcases h with h | h | h
      · refine ⟨(-20-q.1).toNat,by simp [length,List.mem_range]; omega,?_⟩
        simp [routePoint,show (-20-q.1).toNat≤20 by omega]
        ext <;> dsimp <;> omega
      · refine ⟨(1048-q.2).toNat,by simp [length,List.mem_range]; omega,?_⟩
        dsimp [routePoint]
        split_ifs <;> ext <;> dsimp <;> omega
      · refine ⟨(q.1+1092).toNat,by simp [length,List.mem_range]; omega,?_⟩
        dsimp [routePoint]
        split_ifs <;> ext <;> dsimp <;> omega
    · refine ⟨((q.1-(point (edge e).1).1)*(direction e).1+
        (q.2-(point (edge e).1).2)*(direction e).2).toNat,?_,?_⟩
      all_goals
        fin_cases e <;>
          simp only [List.mem_range,Prod.ext_iff] at *
      all_goals try norm_num at he
      all_goals dsimp [length,routePoint,point,edge,direction,OnRoute] at he h ⊢
      all_goals omega

theorem route_in_box (e : Fin 14) (q : Point) (hq : q ∈ route e) : InBox q := by
  rw [route_mem] at hq
  fin_cases e <;> dsimp [OnRoute,edge,point,InBox] at hq ⊢ <;> omega

theorem point_in_box (v : Fin 12) : InBox (point v) := by
  revert v
  decide +kernel

theorem route_vertex_clear (e : Fin 14) (v : Fin 12) :
    point v∈route e ↔ v=(edge e).1 ∨ v=(edge e).2 := by
  rw [route_mem]
  revert e v
  decide +kernel

theorem route_intersection (e f : Fin 14) (hef : e ≠ f) (q : Point)
    (he : q ∈ route e) (hf : q ∈ route f) :
    (q=point (edge e).1 ∨ q=point (edge e).2) ∧
    (q=point (edge f).1 ∨ q=point (edge f).2) := by
  rw [route_mem] at he hf
  fin_cases e <;> fin_cases f <;>
    simp only [Prod.ext_iff] at *
  all_goals dsimp [OnRoute,edge,point] at hef he hf ⊢
  all_goals omega

theorem literal_ports : ∀ j : Fin 3,
    point (PlanarSatAssembly.clauseBottom j)=(0,512*(j.val:Int)+4) ∧
    point (PlanarSatAssembly.clauseTop j)=(0,512*(j.val:Int)-4) := by decide +kernel

theorem backbone_ports : point 8=(0,1028) ∧ point 1=(0,-4) := by decide +kernel

end GridHardness.PlanarSatClause.Lattice
