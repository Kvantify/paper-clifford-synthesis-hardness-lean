/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariablePlacement
public import GridHardness.CorrectedSatIntervalVariableCoreEdges

/-!
# SAT Variable Drawing

The exact induced variable-body subgraph of the completed sweep has
a simultaneous drawing along the outer right boundary. Occurrence links
and the links to sentinel and clause bodies are outside this family.
-/

@[expose] public section

namespace GridHardness.SatVariableDrawing
open PlanarSatAssembly SatVariableOrder SatVariableLattice SatVariablePlacement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

inductive Edge (n : Nat) where
  | direct (v : Fin n)
  | backbone (v w : Fin n) (consecutive : w.val=v.val+1)

def endpoints : Edge n → Vertex n × Vertex n
  | .direct v => ((v,false),(v,true))
  | .backbone v w _ => ((v,true),(w,false))

def route (φ : Formula n m) : Edge n → List Point
  | .direct v => if count φ v=0 then emptyRoute (3*m) (SatVariableOrder.prefix φ v)
      else directRoute (3*m) (SatVariableOrder.prefix φ v)
        (SatVariableOrder.prefix φ v+count φ v)
  | .backbone v _ _ => backboneRoute (3*m) (SatVariableOrder.prefix φ v+count φ v)

theorem endpoint_index (e : Edge n) :
    index (endpoints e).2=index (endpoints e).1+1 := by
  cases e with
  | direct v => simp [endpoints,index]
  | backbone v w h => simp [endpoints,index,h]; omega

theorem source_injective (n : Nat) :
    Function.Injective (fun e : Edge n => (endpoints e).1) := by
  intro e f he
  cases e with
  | direct v =>
    cases f with
    | direct w =>
      have h : v=w := congrArg Prod.fst he
      cases h
      rfl
    | backbone v w h => simp [endpoints] at he
  | backbone v w h =>
    cases f with
    | direct u => simp [endpoints] at he
    | backbone u z hz =>
      have he' : v=u := congrArg Prod.fst he
      subst u
      have hwz : w=z := Fin.ext (by omega)
      subst z
      rfl

theorem route_certificate (φ : Formula n m) (hφ : Regular φ) (e : Edge n) :
    (route φ e).head?=some (vertexPoint φ (endpoints e).1) ∧
    (route φ e).getLast?=some (vertexPoint φ (endpoints e).2) ∧
    (route φ e).Nodup ∧ (route φ e).IsChain UnitStep ∧
    2≤(route φ e).length ∧ (route φ e).length≤512*(3*m)+193 := by
  cases e with
  | direct v =>
    by_cases hc : count φ v=0
    · have h := emptyRoute_certificate (3*m) (SatVariableOrder.prefix φ v)
      simp only [route,endpoints,vertexPoint,point,ite_eq_left hc]
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,by omega,by omega⟩
    · have hp : SatVariableOrder.prefix φ v < SatVariableOrder.prefix φ v+count φ v := by omega
      have h := directRoute_certificate (3*m) _ _ hp
      have hb := prefix_add_count_le φ v
      simp only [route,endpoints,vertexPoint,point,ite_eq_right hc]
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,by omega,by omega⟩
  | backbone v w hw =>
    have hvw : v<w := by change v.val<w.val; omega
    have hp := count_pos_before φ hφ v w hvw
    have hh := consecutive_prefix φ v w hw
    have h := backboneRoute_certificate (3*m) (SatVariableOrder.prefix φ v+count φ v)
    simp only [route,endpoints,vertexPoint,point,ite_eq_right (by omega : ¬count φ v=0),hh]
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,by omega,by omega⟩

/-- Each route is the entire vertical interval between its endpoints. -/
theorem route_mem (φ : Formula n m) (hφ : Regular φ) (e : Edge n) (q : Point) :
    q∈route φ e ↔ q.1=wireX (3*m)+64 ∧
      (vertexPoint φ (endpoints e).1).2≤q.2 ∧
      q.2≤(vertexPoint φ (endpoints e).2).2 := by
  cases e with
  | direct v =>
    by_cases hc : count φ v=0
    · simp only [route,endpoints,vertexPoint,point,ite_eq_left hc,
        emptyRoute,SatCrossingRouting.rising_mem,entry,emptyExit]
      omega
    · have hp : SatVariableOrder.prefix φ v < SatVariableOrder.prefix φ v+count φ v := by omega
      simp only [route,endpoints,vertexPoint,point,ite_eq_right hc,
        directRoute_mem _ _ _ hp,entry,exit]
  | backbone v w hw =>
    have hvw : v<w := by change v.val<w.val; omega
    have hp := count_pos_before φ hφ v w hvw
    have hh := consecutive_prefix φ v w hw
    simp only [route,endpoints,vertexPoint,point,ite_eq_right (by omega : ¬count φ v=0),hh,
      backboneRoute,SatCrossingRouting.rising_mem,entry,exit]
    dsimp [entryY,exitY]
    omega

theorem route_bounds (φ : Formula n m) (hφ : Regular φ) (e : Edge n)
    (q : Point) (hq : q ∈route φ e) :
    q.1=wireX (3*m)+64 ∧ 0≤q.2 ∧ q.2≤512*(3*m:Int)+192 := by
  have hr := (route_mem φ hφ e q).mp hq
  have hs := point_bounds φ (endpoints e).1.1 (endpoints e).1.2
  have ht := point_bounds φ (endpoints e).2.1 (endpoints e).2.2
  change _ ∧ 0≤(vertexPoint φ (endpoints e).1).2 ∧ _ at hs
  change _ ∧ _ ∧ (vertexPoint φ (endpoints e).2).2≤_ at ht
  exact ⟨hr.1,by omega,by omega⟩

theorem route_vertex_clear (φ : Formula n m) (hφ : Regular φ)
    (e : Edge n) (v : Vertex n) :
    vertexPoint φ v∈route φ e ↔ v=(endpoints e).1 ∨ v=(endpoints e).2 := by
  rw [route_mem φ hφ]
  have hi := endpoint_index e
  constructor
  · rintro ⟨_,hl,hu⟩
    have hl' := (y_le_iff φ hφ (endpoints e).1 v).mp hl
    have hu' := (y_le_iff φ hφ v (endpoints e).2).mp hu
    have he : index v=index (endpoints e).1 ∨ index v=index (endpoints e).2 := by omega
    exact he.imp (fun h => index_injective n h) (fun h => index_injective n h)
  · intro he
    have hl : (vertexPoint φ (endpoints e).1).2≤(vertexPoint φ (endpoints e).2).2 :=
      (y_le_iff φ hφ _ _).mpr (by omega)
    rcases he with rfl | rfl <;>
      exact ⟨point_x φ _ _,by omega,by omega⟩

/-- Distinct drawn arcs can meet only at a common endpoint. -/
theorem route_intersection (φ : Formula n m) (hφ : Regular φ)
    (e f : Edge n) (hef : e ≠f) (q : Point)
    (he : q ∈route φ e) (hf : q ∈route φ f) :
    (q=vertexPoint φ (endpoints e).1 ∨ q=vertexPoint φ (endpoints e).2) ∧
    (q=vertexPoint φ (endpoints f).1 ∨ q=vertexPoint φ (endpoints f).2) := by
  have he' := (route_mem φ hφ e q).mp he
  have hf' := (route_mem φ hφ f q).mp hf
  have hie := endpoint_index e
  have hif := endpoint_index f
  have hne : index (endpoints e).1≠index (endpoints f).1 := by
    intro h
    exact hef (source_injective n (index_injective n h))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hi : index (endpoints e).2 ≤ index (endpoints f).1 := by omega
    have hy := (y_le_iff φ hφ _ _).mpr hi
    have hqe : q=vertexPoint φ (endpoints e).2 := by
      apply Prod.ext
      · exact he'.1.trans (point_x φ _ _).symm
      · omega
    have hqf : q=vertexPoint φ (endpoints f).1 := by
      apply Prod.ext
      · exact hf'.1.trans (point_x φ _ _).symm
      · omega
    exact ⟨Or.inr hqe,Or.inl hqf⟩
  · have hi : index (endpoints f).2 ≤ index (endpoints e).1 := by omega
    have hy := (y_le_iff φ hφ _ _).mpr hi
    have hqe : q=vertexPoint φ (endpoints e).1 := by
      apply Prod.ext
      · exact he'.1.trans (point_x φ _ _).symm
      · omega
    have hqf : q=vertexPoint φ (endpoints f).2 := by
      apply Prod.ext
      · exact hf'.1.trans (point_x φ _ _).symm
      · omega
    exact ⟨Or.inl hqe,Or.inr hqf⟩

noncomputable def vertex (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v : Vertex n) : (CorrectedSatInterval.PermutationGraph.graph φ p).Vertex :=
  CorrectedSatInterval.PermutationGraph.liftOriginal φ p (var v.1 v.2)

theorem vertex_injective (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Function.Injective (vertex φ p) := by
  intro u v he
  have h := CorrectedSatInterval.PermutationGraph.liftOriginal_injective φ p he
  simpa only [var,Sum.inr.injEq,Sum.inl.injEq] using h

/-- The drawn arcs are exactly the edges between variable-body vertices
in the actual graph for every occurrence-height permutation. -/
theorem adj_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (u v : Vertex n) :
    (CorrectedSatInterval.PermutationGraph.graph φ p).adj (vertex φ p u) (vertex φ p v) ↔
      ∃ e : Edge n, endpoints e=(u,v) := by
  rcases u with ⟨u,a⟩
  rcases v with ⟨v,b⟩
  rw [show (CorrectedSatInterval.PermutationGraph.graph φ p).adj
      (vertex φ p (u,a)) (vertex φ p (v,b)) ↔
      (u=v ∧ a=false ∧ b=true) ∨ (v.val=u.val+1 ∧ a=true ∧ b=false) from
    CorrectedSatInterval.PermutationGraph.CoreEdges.variable_adj_iff φ p u v a b]
  constructor
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨h,rfl,rfl⟩)
    · exact ⟨.direct _,rfl⟩
    · exact ⟨.backbone u v h,rfl⟩
  · rintro ⟨e,he⟩
    cases e with
    | direct w =>
      simp only [endpoints,Prod.mk.injEq] at he
      rcases he with ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
      exact Or.inl ⟨rfl,rfl,rfl⟩
    | backbone w z h =>
      simp only [endpoints,Prod.mk.injEq] at he
      rcases he with ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
      exact Or.inr ⟨h,rfl,rfl⟩

theorem same_point_iff_same_vertex (φ : Formula n m) (hφ : Regular φ)
    (p : Equiv.Perm (Fin (3 *m))) (u v : Vertex n) :
    vertexPoint φ u=vertexPoint φ v ↔ vertex φ p u=vertex φ p v :=
  ⟨fun h => congrArg _ (point_injective φ hφ h),
    fun h => congrArg _ (vertex_injective φ p h)⟩

end GridHardness.SatVariableDrawing
