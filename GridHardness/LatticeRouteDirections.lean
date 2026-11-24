/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedLocalLayout

/-!
# Lattice Route Directions

Cardinal directions at the endpoints of explicit lattice routes.
Terminal directions point backwards into the route, so both endpoint
directions are outgoing rays suitable for a local vertex replacement.

For simple routes with at least three points the first point after either
endpoint is interior. Endpoint-only intersection therefore forces distinct
incident directions, including when the routes share their other endpoint.
-/

@[expose] public section

namespace GridHardness.LatticeRouteDirections
open CliffordSynthesis DirectedLocalLayout
set_option autoImplicit false

abbrev Point := Int × Int
def UnitStep (p q : Point) : Prop := IntegerGrid.manhattan p q=1

def step (p : Point) (d : Fin 4) : Point :=
  (p.1+(ray d 1).1,p.2+(ray d 1).2)

/-- East, north, west, south, matching `DirectedLocalLayout.ray`.
The function is total; its specification below requires a unit step. -/
def direction (p q : Point) : Fin 4 :=
  if q.1=p.1+1 then 0 else if q.2=p.2+1 then 1 else if q.1=p.1-1 then 2 else 3

theorem step_unit (p : Point) (d : Fin 4) : UnitStep p (step p d) := by
  fin_cases d <;> simp [UnitStep,step,ray,IntegerGrid.manhattan]

theorem step_injective (p : Point) : Function.Injective (step p) := by
  intro d e he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have hr : ray d 1=ray e 1 := by
    apply Prod.ext <;> dsimp [step] at hx hy ⊢ <;> omega
  exact ((ray_eq_ray_iff d e (by decide) (by decide)).mp hr).1

theorem direction_spec (p q : Point) (h : UnitStep p q) : q=step p (direction p q) := by
  rcases (manhattan_one_iff p q).mp h with rfl | rfl | rfl | rfl <;>
    dsimp [direction,step,ray] <;> split_ifs <;> apply Prod.ext <;> dsimp <;> omega

theorem direction_step (p : Point) (d : Fin 4) : direction p (step p d)=d :=
  step_injective p (direction_spec p (step p d) (step_unit p d)).symm

theorem direction_unique (p q : Point) (h : UnitStep p q) (d : Fin 4) :
    q=step p d ↔ direction p q=d := by
  constructor
  · intro he
    exact step_injective p ((direction_spec p q h).symm.trans he)
  · intro he
    exact (direction_spec p q h).trans (congrArg (step p) he)

theorem direction_eq_iff (p q r : Point) (hq : UnitStep p q) (hr : UnitStep p r) :
    direction p q=direction p r ↔ q=r := by
  constructor
  · intro he
    exact (direction_spec p q hq).trans
      ((congrArg (step p) he).trans (direction_spec p r hr).symm)
  · rintro rfl
    rfl

theorem unitStep_symm {p q : Point} (h : UnitStep p q) : UnitStep q p := by
  dsimp [UnitStep,IntegerGrid.manhattan] at h ⊢
  omega

/-- `true` selects the terminal endpoint and reverses the route. -/
def orient (l : List Point) (atEnd : Bool) : List Point := if atEnd then l.reverse else l

@[simp] theorem orient_length (l : List Point) (b : Bool) : (orient l b).length=l.length := by
  cases b <;> simp [orient]

@[simp] theorem mem_orient (l : List Point) (b : Bool) (q : Point) :
    q∈orient l b ↔ q∈l := by cases b <;> simp [orient]

theorem orient_nodup (l : List Point) (b : Bool) (hn : l.Nodup) : (orient l b).Nodup := by
  cases b
  · exact hn
  · exact List.nodup_reverse.mpr hn

theorem orient_chain (l : List Point) (b : Bool) (hc : l.IsChain UnitStep) :
    (orient l b).IsChain UnitStep := by
  cases b
  · exact hc
  · exact List.isChain_reverse.mpr (hc.imp fun _ _ h => unitStep_symm h)

def Endpoint (l : List Point) (q : Point) : Prop := l.head?=some q ∨ l.getLast?=some q

@[simp] theorem endpoint_orient (l : List Point) (b : Bool) (q : Point) :
    Endpoint (orient l b) q ↔ Endpoint l q := by
  cases b <;> simp [Endpoint,orient,List.head?_reverse,List.getLast?_reverse,or_comm]

def endpointPoint (l : List Point) (b : Bool) (hl : 2 ≤l.length) : Point :=
  (orient l b)[0]'(by rw [orient_length]; omega)

def neighborPoint (l : List Point) (b : Bool) (hl : 2 ≤l.length) : Point :=
  (orient l b)[1]'(by rw [orient_length]; omega)

def tangent (l : List Point) (b : Bool) (hl : 2 ≤l.length) : Fin 4 :=
  direction (endpointPoint l b hl) (neighborPoint l b hl)

abbrev initialDirection (l : List Point) (hl : 2 ≤l.length) : Fin 4 := tangent l false hl
abbrev terminalDirection (l : List Point) (hl : 2 ≤l.length) : Fin 4 := tangent l true hl

theorem endpointPoint_spec (l : List Point) (b : Bool) (hl : 2 ≤l.length) :
    (if b then l.getLast? else l.head?)=some (endpointPoint l b hl) := by
  have hh : (orient l b).head?=some (endpointPoint l b hl) := by
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by rw [orient_length]; omega)]
    rfl
  cases b <;> simpa [orient,List.head?_reverse] using hh

theorem endpointPoint_is_endpoint (l : List Point) (b : Bool) (hl : 2 ≤l.length) :
    Endpoint l (endpointPoint l b hl) := by
  have he := endpointPoint_spec l b hl
  cases b
  · exact Or.inl he
  · exact Or.inr he

theorem neighborPoint_mem (l : List Point) (b : Bool) (hl : 2 ≤l.length) :
    neighborPoint l b hl∈l :=
  (mem_orient l b _).mp (List.getElem_mem (by rw [orient_length]; omega))

theorem neighborPoint_step (l : List Point) (b : Bool) (hl : 2 ≤l.length)
    (hc : l.IsChain UnitStep) :
    UnitStep (endpointPoint l b hl) (neighborPoint l b hl) :=
  (List.isChain_iff_getElem.mp (orient_chain l b hc)) 0 (by rw [orient_length]; omega)

theorem tangent_spec (l : List Point) (b : Bool) (hl : 2 ≤l.length)
    (hc : l.IsChain UnitStep) :
    neighborPoint l b hl=step (endpointPoint l b hl) (tangent l b hl) :=
  direction_spec _ _ (neighborPoint_step l b hl hc)

private theorem second_not_endpoint (l : List Point) (hl : 3 ≤l.length) (hn : l.Nodup) :
    ¬Endpoint l (l[1]'(by omega)) := by
  intro he
  have hinj := List.nodup_iff_injective_getElem.mp hn
  rcases he with he | he
  · rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at he
    have hi := congrArg Fin.val
      (hinj (a₁ := ⟨0,by omega⟩) (a₂ := ⟨1,by omega⟩) (Option.some.inj he))
    dsimp at hi
    omega
  · rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by omega)] at he
    have hi := congrArg Fin.val
      (hinj (a₁ := ⟨l.length-1,by omega⟩) (a₂ := ⟨1,by omega⟩) (Option.some.inj he))
    dsimp at hi
    omega

/-- The next point is interior even if the route's far endpoint is also
an endpoint of another incident route. -/
theorem neighborPoint_not_endpoint (l : List Point) (b : Bool)
    (hl : 3 ≤l.length) (hn : l.Nodup) :
    ¬Endpoint l (neighborPoint l b (by omega)) := by
  intro he
  exact second_not_endpoint (orient l b) (by simpa using hl) (orient_nodup l b hn)
    ((endpoint_orient l b _).mpr he)

/-- Existing vertex-clearance certificates immediately make the endpoint
neighbor fresh for every placed graph vertex. -/
theorem neighborPoint_ne_vertex {V : Type*} (point : V → Point)
    (l : List Point) (b : Bool) (hl : 3 ≤l.length) (hn : l.Nodup)
    (hclear : ∀ v, point v ∈l → Endpoint l (point v)) (v : V) :
    neighborPoint l b (by omega)≠point v := by
  intro he
  apply neighborPoint_not_endpoint l b hl hn
  rw [he]
  exact hclear v (he ▸ neighborPoint_mem l b (by omega))

/-- Endpoint-only intersections force distinct rays at any shared endpoint.
The other endpoints may coincide: no distinct-far-endpoint premise is used.
Both terminal and initial incidences are covered by the orientation bits. -/
theorem tangent_ne (l m : List Point) (b c : Bool)
    (hl : 3 ≤l.length) (hm : 3 ≤m.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hpoint : endpointPoint l b (by omega) =endpointPoint m c (by omega))
    (hinter : ∀ q, q ∈l → q ∈m → Endpoint l q ∧ Endpoint m q) :
    tangent l b (by omega)≠tangent m c (by omega) := by
  intro he
  have hl' := tangent_spec l b (by omega) hcl
  have hm' := tangent_spec m c (by omega) hcm
  have hp : neighborPoint l b (by omega)=neighborPoint m c (by omega) := by
    rw [hl',hm',hpoint,he]
  exact neighborPoint_not_endpoint l b hl hn
    (hinter _ (neighborPoint_mem l b (by omega))
      (hp.symm ▸ neighborPoint_mem m c (by omega))).1

theorem initialDirection_ne (l m : List Point)
    (hl : 3 ≤l.length) (hm : 3 ≤m.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hhead : l.head? =m.head?)
    (hinter : ∀ q, q ∈l → q ∈m → Endpoint l q ∧ Endpoint m q) :
    initialDirection l (by omega)≠initialDirection m (by omega) := by
  apply tangent_ne l m false false hl hm hn hcl hcm ?_ hinter
  exact Option.some.inj ((endpointPoint_spec l false (by omega)).symm.trans
    (hhead.trans (endpointPoint_spec m false (by omega))))

theorem terminalDirection_ne (l m : List Point)
    (hl : 3 ≤l.length) (hm : 3 ≤m.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hlast : l.getLast? =m.getLast?)
    (hinter : ∀ q, q ∈l → q ∈m → Endpoint l q ∧ Endpoint m q) :
    terminalDirection l (by omega)≠terminalDirection m (by omega) := by
  apply tangent_ne l m true true hl hm hn hcl hcm ?_ hinter
  exact Option.some.inj ((endpointPoint_spec l true (by omega)).symm.trans
    (hlast.trans (endpointPoint_spec m true (by omega))))

theorem initial_terminal_ne (l m : List Point)
    (hl : 3 ≤l.length) (hm : 3 ≤m.length) (hn : l.Nodup)
    (hcl : l.IsChain UnitStep) (hcm : m.IsChain UnitStep)
    (hhead : l.head? =m.getLast?)
    (hinter : ∀ q, q ∈l → q ∈m → Endpoint l q ∧ Endpoint m q) :
    initialDirection l (by omega)≠terminalDirection m (by omega) := by
  apply tangent_ne l m false true hl hm hn hcl hcm ?_ hinter
  exact Option.some.inj ((endpointPoint_spec l false (by omega)).symm.trans
    (hhead.trans (endpointPoint_spec m true (by omega))))

/-- The incidence labels may encode either incoming or outgoing arcs.
Every family sharing one graph vertex receives distinct cardinal rays,
ready for `DirectedLocalLayout`'s local star and four-path lemmas. -/
theorem incident_tangents_injective {I : Type*} (routes : I → List Point)
    (atEnd : I → Bool) (hl : ∀ i, 3 ≤(routes i).length)
    (hn : ∀ i, (routes i).Nodup) (hc : ∀ i, (routes i).IsChain UnitStep)
    (vertex : Point)
    (hp : ∀ i, endpointPoint (routes i) (atEnd i) (by have := hl i; omega) =vertex)
    (hinter : ∀ i j, i ≠j → ∀ q, q ∈routes i → q ∈routes j →
      Endpoint (routes i) q ∧ Endpoint (routes j) q) :
    Function.Injective (fun i => tangent (routes i) (atEnd i) (by have := hl i; omega)) := by
  intro i j he
  by_contra hij
  exact tangent_ne (routes i) (routes j) (atEnd i) (atEnd j) (hl i) (hl j)
    (hn i) (hc i) (hc j) ((hp i).trans (hp j).symm) (hinter i j hij) he

end GridHardness.LatticeRouteDirections
