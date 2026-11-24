/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetainedDrawing
public import GridHardness.SatCrossingHorizontalSeparation
public import GridHardness.CorrectedSatIntervalHorizontalEdges

/-!
# SAT Horizontal Drawing

Horizontal connections with actual final-graph endpoint names.
The index records two consecutive active columns, so the clearance theorems
apply to every indexed route without a separate scheduling hypothesis.
-/

@[expose] public section

namespace GridHardness.SatHorizontalDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
open SatCrossingHorizontal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Connection {N : Nat} (p : Equiv.Perm (Fin N)) :=
  {t : Fin N × Fin N × Fin N // ConsecutiveColumns p t.1 t.2.1 t.2.2}
abbrev Edge {N : Nat} (p : Equiv.Perm (Fin N)) := Connection p × Bool

variable {N n m : Nat}

def oldCell {p : Equiv.Perm (Fin N)} (c : Connection p) : WireCrossingSchedule.Cell p :=
  ⟨(c.val.1,c.val.2.2),c.property.1⟩

def newCell {p : Equiv.Perm (Fin N)} (c : Connection p) : WireCrossingSchedule.Cell p :=
  ⟨(c.val.2.1,c.val.2.2),c.property.2.1⟩

def oldPort (b : Bool) : RetainedVertex := ⟨XorLine.row 0 (!b),trivial⟩

def newPort (b : Bool) : RetainedVertex :=
  if b then ⟨XorLine.inputPort 4 (.inl false),by decide⟩
  else ⟨XorLine.outputPort 4 (.inl false),by decide⟩

def endpoints {p : Equiv.Perm (Fin N)} (e : Edge p) :
    SatRetainedDrawing.Vertex p × SatRetainedDrawing.Vertex p :=
  if e.2 then ((oldCell e.1,oldPort e.2),(newCell e.1,newPort e.2))
  else ((newCell e.1,newPort e.2),(oldCell e.1,oldPort e.2))

def route (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  connectionRoute p e.1.val.1 e.1.val.2.1 e.1.val.2.2 e.2

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex :=
  SatRetainedDrawing.vertex φ p (endpoints e).1

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex :=
  SatRetainedDrawing.vertex φ p (endpoints e).2

theorem edge_is_arc (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) := by
  obtain ⟨c,b⟩ := e
  cases b
  · exact HorizontalEdges.permutation_outgoing φ p c.val.1 c.val.2.1 c.val.2.2 c.property
  · exact HorizontalEdges.permutation_incoming φ p c.val.1 c.val.2.1 c.val.2.2 c.property

theorem route_endpoints (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (SatRetainedDrawing.point p (endpoints e).1) ∧
    (route p e).getLast? = some (SatRetainedDrawing.point p (endpoints e).2) := by
  obtain ⟨c,b⟩ := e
  have h := SatCrossingHorizontal.route_endpoints p c.val.1 c.val.2.1 c.val.2.2
    c.property.2.2.1
  cases b
  · exact ⟨h.2.2.1,h.2.2.2⟩
  · exact ⟨h.1,h.2.1⟩

theorem route_simple (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep := by
  obtain ⟨c,b⟩ := e
  have h := SatCrossingHorizontal.route_simple p c.val.1 c.val.2.1 c.val.2.2
  cases b
  · exact h.2.2
  · exact ⟨h.1,h.2.1⟩

theorem route_length (p : Equiv.Perm (Fin N)) (e : Edge p) :
    409 ≤ (route p e).length ∧ (route p e).length ≤ 512*N := by
  obtain ⟨c,b⟩ := e
  have h := route_length_bounds p c.val.1 c.val.2.1 c.val.2.2 c.property.2.2.1
  cases b
  · exact h.2.2
  · exact ⟨h.1,h.2.1⟩

theorem actual_route_certificate (φ : Formula n m)
    (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    409 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 1536*m := by
  have he := route_endpoints (SatClauseOrder.permutation φ) e
  have hs := route_simple (SatClauseOrder.permutation φ) e
  have hl := route_length (SatClauseOrder.permutation φ) e
  simpa only [source,target,SatRetainedDrawing.actualPoint_vertex,← Nat.mul_assoc] using
    And.intro he.1 (And.intro he.2 (And.intro hs.1 (And.intro hs.2 hl)))

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*N+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+522 :=
  route_coordinates_bounded p e.1.val.1 e.1.val.2.1 e.1.val.2.2 e.1.property.2.2.1 q
    (connectionRoute_mem p _ _ _ e.2 q hq)

theorem separation (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f)
    (q t : Point) (hq : q ∈ route p e) (ht : t ∈ route p f) :
    8 ≤ IntegerGrid.manhattan q t := by
  apply global_separation p e.1.val.1 e.1.val.2.1 e.1.val.2.2
    f.1.val.1 f.1.val.2.1 f.1.val.2.2 e.2 f.2 e.1.property f.1.property _ q t hq ht
  intro he
  apply hne
  obtain ⟨hi,h⟩ := Prod.mk.inj he
  obtain ⟨hk,h⟩ := Prod.mk.inj h
  obtain ⟨hj,hb⟩ := Prod.mk.inj h
  exact Prod.ext (Subtype.ext (Prod.ext hi (Prod.ext hk hj))) hb

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
  obtain ⟨c,b⟩ := e
  by_cases ho : v.1 = oldCell c
  · have h' := h
    change SatCrossingLattice.point p v.1.val v.2.val ∈ _ at h'
    rw [ho] at h'
    have hh := old_vertices_clear p c.val.1 c.val.2.1 c.val.2.2 c.property.2.2.1 v.2
    cases b
    · exact Or.inr (Prod.ext ho (Subtype.ext (hh.2.mp h')))
    · exact Or.inl (Prod.ext ho (Subtype.ext (hh.1.mp h')))
  · by_cases hn : v.1 = newCell c
    · have h' := h
      change SatCrossingLattice.point p v.1.val v.2.val ∈ _ at h'
      rw [hn] at h'
      have hh := new_vertices_clear p c.val.1 c.val.2.1 c.val.2.2 c.property.2.2.1 v.2.val
      cases b
      · exact Or.inl (Prod.ext hn (Subtype.ext (hh.2.mp h')))
      · exact Or.inr (Prod.ext hn (Subtype.ext (hh.1.mp h')))
    · have hh := other_box_separated p c.val.1 c.val.2.1 c.val.2.2 c.property
        v.1.val v.1.property
        (fun he => ho (Subtype.ext he)) (fun he => hn (Subtype.ext he))
        _ _ (connectionRoute_mem p _ _ _ b _ h)
        (SatCrossingLattice.point_in_box p v.1.val v.2.val)
      simp [SatRetainedDrawing.point,IntegerGrid.manhattan] at hh

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
      have hd := SatCrossingRetirement.Sides.horizontal_disjoint p i e.1.val.1
        e.1.val.2.1 e.1.val.2.2 s e.1.property
      obtain ⟨c,b⟩ := e
      cases b
      · exact False.elim (List.disjoint_left.mp hd.2 hm h)
      · exact False.elim (List.disjoint_left.mp hd.1 hm h)
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

/-- A connector meets a retained internal route only at one of the
connector's two ports. The retained family is restricted to active cells. -/
theorem retained_route_intersection (p : Equiv.Perm (Fin N))
    (e : Edge p) (f : SatRetainedDrawing.Edge p) (q : Point)
    (he : q ∈ route p e) (hf : q ∈ SatRetainedDrawing.route p f) :
    q = SatRetainedDrawing.point p (endpoints e).1 ∨
    q = SatRetainedDrawing.point p (endpoints e).2 := by
  obtain ⟨c,b⟩ := e
  by_cases ho : f.1 = oldCell c
  · change q ∈ SatCrossingLattice.route p f.1.val f.2.val at hf
    rw [ho] at hf
    cases b
    · exact Or.inr ((lower_old_edge_intersection p c.val.1 c.val.2.1 c.val.2.2
        c.property.2.2.1 f.2.val f.2.property q).mp ⟨he,hf⟩).1
    · exact Or.inl ((upper_old_edge_intersection p c.val.1 c.val.2.1 c.val.2.2
        c.property.2.2.1 f.2.val f.2.property q).mp ⟨he,hf⟩).1
  · by_cases hn : f.1 = newCell c
    · change q ∈ SatCrossingLattice.route p f.1.val f.2.val at hf
      rw [hn] at hf
      cases b
      · exact Or.inl ((lower_new_edge_intersection p c.val.1 c.val.2.1 c.val.2.2
          c.property.2.2.1 f.2.val q).mp ⟨he,hf⟩).1
      · exact Or.inr ((upper_new_edge_intersection p c.val.1 c.val.2.1 c.val.2.2
          c.property.2.2.1 f.2.val q).mp ⟨he,hf⟩).1
    · have hh := other_box_separated p c.val.1 c.val.2.1 c.val.2.2 c.property
        f.1.val f.1.property
        (fun h => ho (Subtype.ext h)) (fun h => hn (Subtype.ext h))
        q q (connectionRoute_mem p _ _ _ b q he)
        (SatCrossingLattice.route_in_box p f.1.val f.2.val q hf)
      simp [IntegerGrid.manhattan] at hh

/-- Every mixed connector/internal-route intersection is the image of a
single actual graph vertex incident with both routes. -/
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

end GridHardness.SatHorizontalDrawing
