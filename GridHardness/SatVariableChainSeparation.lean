/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableChainDrawing
public import GridHardness.SatVariableDrawing

/-!
# SAT Variable Chain Separation

Separation of all variable occurrence-chain routes, and their exact
intersections with the variable-body drawing. The eight-step gaps between
input and output ports keep distinct chain routes disjoint.
-/

@[expose] public section

namespace GridHardness.SatVariableChainSeparation
open CliffordSynthesis PlanarSatAssembly SatVariableOrder SatVariableLattice
open SatVariableChainDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
variable {n m : Nat}

/-- The exact vertical interval occupied by a chain route. -/
def interval {φ : Formula n m} : Edge φ → Int × Int
  | .entry v _ =>
    (512*(SatVariableOrder.prefix φ v:Int)+128,
      512*((SatVariableOrder.prefix φ v:Int)+1)-4)
  | .between v k _ _ =>
    (512*((SatVariableOrder.prefix φ v:Int)+k.val+1)+4,
      512*((SatVariableOrder.prefix φ v:Int)+k.val+2)-4)
  | .exit v _ =>
    (512*((SatVariableOrder.prefix φ v:Int)+count φ v)+4,
      512*((SatVariableOrder.prefix φ v:Int)+count φ v)+64)

theorem route_height {φ : Formula n m} (e : Edge φ) (q : Point)
    (hq : q ∈route e) : (interval e).1≤q.2 ∧ q.2≤(interval e).2 := by
  cases e with
  | entry v h =>
    have hr := entryRoute_bounds (3*m) (SatVariableOrder.prefix φ v) q hq
    exact ⟨hr.2.2.1,hr.2.2.2⟩
  | between v k l h =>
    have hr := (SatCrossingRouting.rising_mem _ _ _ q).mp hq
    have hk := variableRank_indexed φ v k
    dsimp [interval]
    omega
  | exit v h =>
    have hr := exitRoute_bounds (3*m) (SatVariableOrder.prefix φ v+count φ v) q hq
    dsimp [exitY,interval] at hr ⊢
    omega

theorem owner_block_bounds {φ : Formula n m} (e : Edge φ) :
    512*(SatVariableOrder.prefix φ (owner e):Int)+128≤(interval e).1 ∧
      (interval e).2≤512*((SatVariableOrder.prefix φ (owner e):Int)+count φ (owner e))+64 := by
  cases e with
  | entry v h => dsimp [interval,owner]; omega
  | between v k l h =>
    have hk := k.isLt
    have hl := l.isLt
    dsimp [interval,owner]
    omega
  | exit v h => dsimp [interval,owner]; omega

theorem different_owner_intervals {φ : Formula n m} (e f : Edge φ)
    (h : owner e < owner f) : (interval e).2+64≤(interval f).1 := by
  have he := owner_block_bounds e
  have hf := owner_block_bounds f
  have ho := blocks_ordered φ h
  omega

theorem same_owner_intervals {φ : Formula n m} (e f : Edge φ)
    (he : owner e =owner f) (hef : e ≠f) :
    (interval e).2+8≤(interval f).1 ∨ (interval f).2+8≤(interval e).1 := by
  cases e with
  | entry v hv =>
    cases f with
    | entry w hw =>
      have he' : v=w := he
      subst w
      exact False.elim (hef rfl)
    | between w k l h =>
      have he' : v=w := he
      subst w
      left
      dsimp [interval]
      omega
    | exit w hw =>
      have he' : v=w := he
      subst w
      left
      dsimp [interval]
      omega
  | between v k l h =>
    cases f with
    | entry w hw =>
      have he' : v=w := he
      subst w
      right
      dsimp [interval]
      omega
    | between w a b hab =>
      have he' : v=w := he
      subst w
      have hka : k.val≠a.val := by
        intro he
        have hk : k=a := Fin.ext he
        have hl : l=b := Fin.ext (by omega)
        subst a
        subst b
        exact hef rfl
      dsimp [interval]
      omega
    | exit w hw =>
      have he' : v=w := he
      subst w
      have hl := l.isLt
      left
      dsimp [interval]
      omega
  | exit v hv =>
    cases f with
    | entry w hw =>
      have he' : v=w := he
      subst w
      right
      dsimp [interval]
      omega
    | between w k l h =>
      have he' : v=w := he
      subst w
      have hl := l.isLt
      right
      dsimp [interval]
      omega
    | exit w hw =>
      have he' : v=w := he
      subst w
      exact False.elim (hef rfl)

/-- Every pair of distinct chain routes is separated by at least eight
unit steps. This requires no restriction on unused variable blocks. -/
theorem routes_separated {φ : Formula n m} (e f : Edge φ) (hef : e ≠f)
    (q r : Point) (hq : q ∈route e) (hr : r ∈route f) :
    8≤IntegerGrid.manhattan q r := by
  have hq' := route_height e q hq
  have hr' := route_height f r hr
  rcases lt_trichotomy (owner e) (owner f) with h | h | h
  · have ho := different_owner_intervals e f h
    dsimp [IntegerGrid.manhattan]
    omega
  · have ho := same_owner_intervals e f h hef
    dsimp [IntegerGrid.manhattan]
    omega
  · have ho := different_owner_intervals f e h
    dsimp [IntegerGrid.manhattan]
    omega

theorem routes_disjoint {φ : Formula n m} (e f : Edge φ) (hef : e ≠f) :
    (route e).Disjoint (route f) := by
  apply List.disjoint_left.mpr
  intro q hq hr
  have h := routes_separated e f hef q q hq hr
  simp [IntegerGrid.manhattan] at h

/-- A chain route reaches the variable-body line only at its own entry
or exit vertex. The links between consecutive wires never reach that line. -/
theorem outer_boundary_intersection (φ : Formula n m) (e : Edge φ)
    (q : Point) (hq : q ∈route e) (hx : q.1 =wireX (3 *m) +64) :
    ∃ z : SatVariablePlacement.Vertex n,
      ((endpoints e).1=.inl z ∨ (endpoints e).2=.inl z) ∧
        q=SatVariablePlacement.vertexPoint φ z := by
  cases e with
  | entry v h =>
    refine ⟨(v,false),Or.inl rfl,?_⟩
    have hr := (entryRoute_mem (3*m) (SatVariableOrder.prefix φ v) q).mp hq
    change q=entry (3*m) (SatVariableOrder.prefix φ v)
    rcases hr with hr | hr <;> apply Prod.ext <;> dsimp [entry] <;> omega
  | between v k l h =>
    have hr := (SatCrossingRouting.rising_mem _ _ _ q).mp hq
    omega
  | exit v h =>
    refine ⟨(v,true),Or.inr rfl,?_⟩
    have hr := (exitRoute_mem (3*m) (SatVariableOrder.prefix φ v+count φ v) q).mp hq
    simp only [SatVariablePlacement.vertexPoint,SatVariablePlacement.point,
      ite_eq_right (by omega : ¬count φ v=0)]
    rcases hr with hr | hr <;> apply Prod.ext <;> dsimp [exit] <;> omega

/-- The chain and variable-body families can meet only at a vertex which
is an endpoint of both edges. -/
theorem body_route_intersection (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (p : Equiv.Perm (Fin (3 *m))) (e : Edge φ) (f : SatVariableDrawing.Edge n)
    (q : Point) (he : q ∈route e) (hf : q ∈SatVariableDrawing.route φ f) :
    (q=point φ p (endpoints e).1 ∨ q=point φ p (endpoints e).2) ∧
      (q=SatVariablePlacement.vertexPoint φ (SatVariableDrawing.endpoints f).1 ∨
        q=SatVariablePlacement.vertexPoint φ (SatVariableDrawing.endpoints f).2) := by
  have hr := (SatVariableDrawing.route_mem φ hφ f q).mp hf
  obtain ⟨z,hz,hq⟩ := outer_boundary_intersection φ e q he hr.1
  constructor
  · rcases hz with hz | hz
    · exact Or.inl (hq.trans (congrArg (point φ p) hz).symm)
    · exact Or.inr (hq.trans (congrArg (point φ p) hz).symm)
  · rw [hq] at hf
    have hz := (SatVariableDrawing.route_vertex_clear φ hφ f z).mp hf
    exact hz.imp (fun h => hq.trans (congrArg (SatVariablePlacement.vertexPoint φ) h))
      (fun h => hq.trans (congrArg (SatVariablePlacement.vertexPoint φ) h))

end GridHardness.SatVariableChainSeparation
