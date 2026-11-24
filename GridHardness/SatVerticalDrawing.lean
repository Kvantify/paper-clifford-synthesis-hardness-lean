/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetainedDrawing
public import GridHardness.SatCrossingVerticalEdgeClearance

/-!
# SAT Vertical Drawing

Vertical connections between consecutive active crossings, expressed
in the common vertex placement.  All four directed row lanes have simple,
bounded routes.  Their only graph vertices are their named endpoints, and
distinct vertical routes are separated by at least twenty lattice steps.
The adjacency of these endpoint pairs in the final graph is a separate
semantic obligation; this module proves their geometric properties.
-/

@[expose] public section

namespace GridHardness.SatVerticalDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Connection {N : Nat} (p : Equiv.Perm (Fin N)) :=
  {t : Fin N × Fin N × Fin N // SatCrossingRouting.Consecutive p t.1 t.2.1 t.2.2}
abbrev Edge {N : Nat} (p : Equiv.Perm (Fin N)) := Connection p × Fin 4

variable {N n m : Nat}

def lowerCell {p : Equiv.Perm (Fin N)} (c : Connection p) : WireCrossingSchedule.Cell p :=
  ⟨(c.val.1,c.val.2.1),c.property.1⟩

def upperCell {p : Equiv.Perm (Fin N)} (c : Connection p) : WireCrossingSchedule.Cell p :=
  ⟨(c.val.1,c.val.2.2),c.property.2.1⟩

def inputPort (r : Fin 4) : SatCrossingHorizontal.RetainedVertex :=
  ⟨XorLine.inputPort 4 (.inr r),by fin_cases r <;> decide⟩

def outputPort (r : Fin 4) : SatCrossingHorizontal.RetainedVertex :=
  ⟨XorLine.outputPort 4 (.inr r),by fin_cases r <;> decide⟩

def endpoints {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatRetainedDrawing.Vertex p × SatRetainedDrawing.Vertex p :=
  if e.2.val%2=0 then
    ((upperCell e.1,outputPort e.2),(lowerCell e.1,inputPort e.2))
  else ((lowerCell e.1,outputPort e.2),(upperCell e.1,inputPort e.2))

def route (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  SatCrossingRouting.route p e.1.val.1 e.1.val.2.1 e.1.val.2.2 e.2

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex :=
  SatRetainedDrawing.vertex φ p (endpoints e).1

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex :=
  SatRetainedDrawing.vertex φ p (endpoints e).2

theorem route_endpoints (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (SatRetainedDrawing.point p (endpoints e).1) ∧
    (route p e).getLast? = some (SatRetainedDrawing.point p (endpoints e).2) := by
  have h := SatCrossingRouting.route_endpoints p e.1.val.1 e.1.val.2.1 e.1.val.2.2
    e.1.property.2.2.1 e.2
  by_cases hr : e.2.val%2=0 <;>
    simpa only [route,endpoints,hr,ite_true,ite_false,SatRetainedDrawing.point,
      lowerCell,upperCell,inputPort,outputPort] using h

theorem route_simple (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep :=
  ⟨SatCrossingRouting.route_nodup p _ _ _ _,SatCrossingRouting.route_chain p _ _ _ _⟩

theorem route_length (p : Equiv.Perm (Fin N)) (e : Edge p) :
    493 ≤ (route p e).length ∧ (route p e).length ≤ 512*N :=
  SatCrossingRouting.route_length_bounds p _ _ _ e.1.property.2.2.1 _

theorem actual_route_certificate (φ : Formula n m)
    (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    493 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 1536*m := by
  have he := route_endpoints (SatClauseOrder.permutation φ) e
  have hs := route_simple (SatClauseOrder.permutation φ) e
  have hl := route_length (SatClauseOrder.permutation φ) e
  simpa only [source,target,SatRetainedDrawing.actualPoint_vertex,← Nat.mul_assoc] using
    And.intro he.1 (And.intro he.2 (And.intro hs.1 (And.intro hs.2 hl)))

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*N+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+522 :=
  SatCrossingRouting.route_coordinates_bounded p _ _ _ e.1.property.2.2.1 _ q hq

theorem separation (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f)
    (q t : Point) (hq : q ∈ route p e) (ht : t ∈ route p f) :
    20 ≤ IntegerGrid.manhattan q t := by
  apply SatCrossingRouting.global_separation p e.1.val.1 e.1.val.2.1 e.1.val.2.2
    f.1.val.1 f.1.val.2.1 f.1.val.2.2 e.2 f.2 e.1.property f.1.property _ q t hq ht
  intro he
  apply hne
  obtain ⟨hi,h⟩ := Prod.mk.inj he
  obtain ⟨hj,h⟩ := Prod.mk.inj h
  obtain ⟨hk,hr⟩ := Prod.mk.inj h
  exact Prod.ext (Subtype.ext (Prod.ext hi (Prod.ext hj hk))) hr

theorem routes_disjoint (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f) :
    (route p e).Disjoint (route p f) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have h := separation p e f hne q q hq ht
  simp [IntegerGrid.manhattan] at h

theorem retained_vertex_intersection (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatRetainedDrawing.Vertex p)
    (h : SatRetainedDrawing.point p v ∈ route p e) :
    v = (endpoints e).1 ∨ v = (endpoints e).2 := by
  have hv := (SatCrossingRouting.route_vertex_clear p e.1.val.1 e.1.val.2.1
    e.1.val.2.2 e.1.property e.2 v.1.val v.1.property v.2.val).mp h
  rcases hv with ⟨hc,hv⟩ | ⟨hc,hv⟩
  · have hc' : v.1 = lowerCell e.1 := Subtype.ext hc
    by_cases hr : e.2.val%2=0
    · apply Or.inr
      simp only [endpoints,hr,ite_true]
      apply Prod.ext hc'
      apply Subtype.ext
      simpa only [SatCrossingRouting.lowerPort,hr,ite_true,endpoints,inputPort] using hv
    · apply Or.inl
      simp only [endpoints,hr,ite_false]
      apply Prod.ext hc'
      apply Subtype.ext
      simpa only [SatCrossingRouting.lowerPort,hr,ite_false,endpoints,outputPort] using hv
  · have hc' : v.1 = upperCell e.1 := Subtype.ext hc
    by_cases hr : e.2.val%2=0
    · apply Or.inl
      simp only [endpoints,hr,ite_true]
      apply Prod.ext hc'
      apply Subtype.ext
      simpa only [SatCrossingRouting.upperPort,hr,ite_true,endpoints,outputPort] using hv
    · apply Or.inr
      simp only [endpoints,hr,ite_false]
      apply Prod.ext hc'
      apply Subtype.ext
      simpa only [SatCrossingRouting.upperPort,hr,ite_false,endpoints,inputPort] using hv

private theorem side_incident : ∀ v : Fin 8, ∃ e : Fin 6,
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).1 ∨
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).2 := by decide +kernel

theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ route p e ↔
      v = .inr (endpoints e).1 ∨ v = .inr (endpoints e).2 := by
  constructor
  · intro h
    cases v with
    | inl iv =>
      obtain ⟨i,v⟩ := iv
      obtain ⟨s,hs⟩ := side_incident v
      have hm := (SatCrossingRetirement.Sides.route_vertex_clear p i s v).mpr hs
      exact False.elim (List.disjoint_left.mp
        (SatCrossingRetirement.Sides.vertical_disjoint p i e.1.val.1
          e.1.val.2.1 e.1.val.2.2 s e.2 e.1.property) hm h)
    | inr v =>
      exact (retained_vertex_intersection p e v h).imp (congrArg Sum.inr) (congrArg Sum.inr)
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (route_endpoints p e).1
    · exact List.mem_of_getLast? (route_endpoints p e).2

theorem body_vertex_clear (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ))
    (v : PermutationWirePlacement.BodyVertex n m) :
    SatGlobalVertexPlacement.bodyPoint φ v ∉ route (SatClauseOrder.permutation φ) e := by
  intro h
  have hb := route_bounds (SatClauseOrder.permutation φ) e _ h
  rcases v with i | ⟨v,b⟩ | ⟨c,v⟩
  · fin_cases i <;> dsimp [SatGlobalVertexPlacement.bodyPoint,SatExteriorLattice.sentinel,
      SatVariableLattice.wireX] at hb <;> omega
  · have hx := SatVariablePlacement.point_x φ v b
    dsimp [SatGlobalVertexPlacement.bodyPoint,SatVariableLattice.wireX] at hb hx
    omega
  · have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
    change 0 ≤ (SatClauseOrder.point c v).1 ∧ _ at hb
    omega

theorem actual_vertex_clear (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ))
    (v : (SatClauseOrder.graph φ).Vertex) :
    SatGlobalVertexPlacement.actualPoint φ v ∈ route (SatClauseOrder.permutation φ) e ↔
      v = source φ (SatClauseOrder.permutation φ) e ∨
      v = target φ (SatClauseOrder.permutation φ) e := by
  obtain ⟨z,rfl⟩ := (SatGlobalVertexPlacement.equiv φ).surjective v
  rw [SatGlobalVertexPlacement.actualPoint_equiv]
  cases z with
  | inl b =>
    constructor
    · exact fun h => False.elim (body_vertex_clear φ e b h)
    · rintro (h | h)
      all_goals
        have he := congrArg (SatGlobalVertexPlacement.actualPoint φ) h
        rw [SatGlobalVertexPlacement.actualPoint_equiv] at he
      · exact he.symm ▸ List.mem_of_head? (actual_route_certificate φ e).1
      · exact he.symm ▸ List.mem_of_getLast? (actual_route_certificate φ e).2.1
  | inr w =>
    change SatCrossingWireVertices.point _ w ∈ _ ↔ _
    rw [wire_vertex_clear]
    have hs : SatGlobalVertexPlacement.equiv φ (.inr (.inr (endpoints e).1)) =
        source φ (SatClauseOrder.permutation φ) e := by
      rw [SatGlobalVertexPlacement.equiv_wire,PermutationWirePlacement.vertex_fresh]
      rfl
    have ht : SatGlobalVertexPlacement.equiv φ (.inr (.inr (endpoints e).2)) =
        target φ (SatClauseOrder.permutation φ) e := by
      rw [SatGlobalVertexPlacement.equiv_wire,PermutationWirePlacement.vertex_fresh]
      rfl
    rw [← hs,← ht]
    simp only [Equiv.apply_eq_iff_eq,Sum.inr.injEq]

/-- A vertical connector meets a retained local route only at one of its
two boundary ports. -/
theorem retained_route_intersection (p : Equiv.Perm (Fin N))
    (e : Edge p) (f : SatRetainedDrawing.Edge p) (q : Point)
    (he : q ∈ route p e) (hf : q ∈ SatRetainedDrawing.route p f) :
    q = SatRetainedDrawing.point p (endpoints e).1 ∨
    q = SatRetainedDrawing.point p (endpoints e).2 := by
  have h := (SatCrossingRouting.edge_intersection_iff p e.1.val.1 e.1.val.2.1
    e.1.val.2.2 e.1.property e.2 f.1.val f.1.property f.2.val q).mp ⟨he,hf⟩
  rcases h with ⟨_,h,_⟩ | ⟨_,h,_⟩
  · by_cases hr : e.2.val%2=0
    · apply Or.inr
      simpa only [SatCrossingRouting.lowerPort,hr,ite_true,endpoints,
        SatRetainedDrawing.point,lowerCell,inputPort] using h
    · apply Or.inl
      simpa only [SatCrossingRouting.lowerPort,hr,ite_false,endpoints,
        SatRetainedDrawing.point,lowerCell,outputPort] using h
  · by_cases hr : e.2.val%2=0
    · apply Or.inl
      simpa only [SatCrossingRouting.upperPort,hr,ite_true,endpoints,
        SatRetainedDrawing.point,upperCell,outputPort] using h
    · apply Or.inr
      simpa only [SatCrossingRouting.upperPort,hr,ite_false,endpoints,
        SatRetainedDrawing.point,upperCell,inputPort] using h

theorem retained_shared_vertex (φ : Formula n m)
    (e : Edge (SatClauseOrder.permutation φ))
    (f : SatRetainedDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatRetainedDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex,
      (v = source φ (SatClauseOrder.permutation φ) e ∨
        v = target φ (SatClauseOrder.permutation φ) e) ∧
      (v = SatRetainedDrawing.source φ (SatClauseOrder.permutation φ) f ∨
        v = SatRetainedDrawing.target φ (SatClauseOrder.permutation φ) f) ∧
      q = SatGlobalVertexPlacement.actualPoint φ v := by
  have h := retained_route_intersection (SatClauseOrder.permutation φ) e f q he hf
  have hs : SatRetainedDrawing.point (SatClauseOrder.permutation φ) (endpoints e).1 =
      SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e) :=
    (SatRetainedDrawing.actualPoint_vertex φ (endpoints e).1).symm
  have ht : SatRetainedDrawing.point (SatClauseOrder.permutation φ) (endpoints e).2 =
      SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e) :=
    (SatRetainedDrawing.actualPoint_vertex φ (endpoints e).2).symm
  rw [hs,ht] at h
  rcases h with h | h
  · refine ⟨source φ (SatClauseOrder.permutation φ) e,Or.inl rfl,?_,h⟩
    exact (SatRetainedDrawing.actual_vertex_clear φ f _).mp (h ▸ hf)
  · refine ⟨target φ (SatClauseOrder.permutation φ) e,Or.inr rfl,?_,h⟩
    exact (SatRetainedDrawing.actual_vertex_clear φ f _).mp (h ▸ hf)

end GridHardness.SatVerticalDrawing
