/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetiredSideEdges
public import GridHardness.SatRetainedDrawing

/-!
# SAT Retired Side Drawing

Actual final-graph routes for the six nonmandatory edges of every
retired occurrence XOR. These short routes use the common vertex placement,
avoid every unrelated final vertex, and meet each other only at common
endpoints. The mandatory residual edges are a separate family.
-/

@[expose] public section

namespace GridHardness.SatRetiredSideDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev Vertex (N : Nat) := Fin N × Fin 8
abbrev Edge {N : Nat} (_p : Equiv.Perm (Fin N)) := Fin N × Fin 6

def localEndpoints (e : Fin 6) : Fin 8 × Fin 8 :=
  XorGadget.arc (SatCrossingRetirement.sideArc e)

theorem localEndpoints_injective : Function.Injective localEndpoints := by decide +kernel

def endpoints {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) : Vertex N × Vertex N :=
  ((e.1,(localEndpoints e.2).1),(e.1,(localEndpoints e.2).2))

def point {N : Nat} (p : Equiv.Perm (Fin N)) (v : Vertex N) : Point :=
  SatCrossingRetirement.Sides.xorPoint p v.1 v.2

def route {N : Nat} (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  SatCrossingRetirement.Sides.route p e.1 e.2

variable {N n m : Nat}

noncomputable def vertex (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (v : Vertex (3 *m)) :
    (PermutationGraph.graph φ p).Vertex := PermutationWirePlacement.vertex φ p (.inl v)

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := vertex φ p (endpoints e).1

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := vertex φ p (endpoints e).2

/-- Among nonmandatory candidate pairs, the six local indices enumerate
exactly the actual final adjacencies. The four mandatory candidates can
instead be subdivided into residual edges and are excluded explicitly. -/
theorem same_wire_nonmandatory_adj_iff (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (j : Fin (3 *m)) (u v : Fin 8)
    (h : RetiredSideEdges.Nonmandatory u v) :
    (PermutationGraph.graph φ p).adj (vertex φ p (j,u)) (vertex φ p (j,v)) ↔
      ∃ e : Fin 6, localEndpoints e = (u,v) :=
  RetiredSideEdges.placement_nonmandatory_iff φ p j u v h

theorem edge_is_arc (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) :=
  RetiredSideEdges.placement_side_edge φ p e.1 e.2

theorem actualPoint_vertex (φ : Formula n m) (v : Vertex (3 *m)) :
    SatGlobalVertexPlacement.actualPoint φ (vertex φ (SatClauseOrder.permutation φ) v) =
      point (SatClauseOrder.permutation φ) v := by
  rw [vertex,SatGlobalVertexPlacement.actualPoint_wire]
  rfl

theorem route_certificate (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (point p (endpoints e).1) ∧
    (route p e).getLast? = some (point p (endpoints e).2) ∧
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep ∧
    3 ≤ (route p e).length ∧ (route p e).length ≤ 5 :=
  ⟨(SatCrossingRetirement.Sides.route_endpoints p e.1 e.2).1,
    (SatCrossingRetirement.Sides.route_endpoints p e.1 e.2).2,
    (SatCrossingRetirement.Sides.route_simple p e.1 e.2).1,
    (SatCrossingRetirement.Sides.route_simple p e.1 e.2).2,
    SatCrossingRetirement.Sides.route_length p e.1 e.2⟩

theorem actual_route_certificate (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    3 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 5 := by
  simpa only [source,target,actualPoint_vertex] using route_certificate (SatClauseOrder.permutation φ) e

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*(N+1)+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+516 :=
  SatCrossingRetirement.Sides.route_bounds p e.1 e.2 q hq

private theorem side_incident : ∀ v : Fin 8, ∃ e : Fin 6,
    v = (localEndpoints e).1 ∨ v = (localEndpoints e).2 := by decide +kernel

-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- The geometric proof unfolds the coordinates of the constructed routes.
private theorem retained_incident : ∀ v : SatCrossingHorizontal.RetainedVertex,
    ∃ e : Fin 66, SatCrossingHorizontal.RetainedEdge e ∧
      (v.val = (XorLine.Lattice.edge e).1 ∨ v.val = (XorLine.Lattice.edge e).2) := by
  decide +kernel

theorem placed_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p) (v : Vertex N) :
    point p v ∈ route p e ↔ v = (endpoints e).1 ∨ v = (endpoints e).2 := by
  by_cases hj : v.1 = e.1
  · rcases e with ⟨j,e⟩
    rcases v with ⟨k,v⟩
    dsimp at hj
    subst k
    change SatCrossingRetirement.Sides.xorPoint p j v ∈
      SatCrossingRetirement.Sides.route p j e ↔ _
    rw [SatCrossingRetirement.Sides.route_vertex_clear]
    constructor
    · exact fun h => h.imp (Prod.ext rfl) (Prod.ext rfl)
    · exact fun h => h.imp (congrArg Prod.snd) (congrArg Prod.snd)
  · constructor
    · intro h
      obtain ⟨s,hs⟩ := side_incident v.2
      have hv := (SatCrossingRetirement.Sides.route_vertex_clear p v.1 s v.2).mpr hs
      exact False.elim (List.disjoint_left.mp
        (SatCrossingRetirement.Sides.different_wire_sides p v.1 e.1 hj s e.2) hv h)
    · rintro (h | h) <;> exact False.elim (hj (congrArg Prod.fst h))

theorem retained_routes_disjoint (p : Equiv.Perm (Fin N)) (e : Edge p)
    (f : SatRetainedDrawing.Edge p) :
    (route p e).Disjoint (SatRetainedDrawing.route p f) :=
  SatCrossingRetirement.Sides.retained_routes_disjoint p e.1 e.2 f.1.val f.2.val
    f.2.property.1 f.2.property.2

theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ route p e ↔
      v = .inl (endpoints e).1 ∨ v = .inl (endpoints e).2 := by
  cases v with
  | inl v =>
    simpa only [SatCrossingWireVertices.point,point,SatCrossingWireVertices.retired,
      SatCrossingRetirement.Sides.xorPoint,SatCrossingRetirement.Residual.rowEnd,
      Sum.inl.injEq] using placed_vertex_clear p e v
  | inr v =>
    simp only [reduceCtorEq,or_self,iff_false]
    intro h
    obtain ⟨i,hi,hv⟩ := retained_incident v.2
    have hm := (SatCrossingLattice.route_vertex_clear p v.1.val i v.2.val).mpr hv
    exact List.disjoint_left.mp
      (retained_routes_disjoint p e (v.1,⟨i,hi⟩)) h hm

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
    have hs : SatGlobalVertexPlacement.equiv φ (.inr (.inl (endpoints e).1)) =
        source φ (SatClauseOrder.permutation φ) e := rfl
    have ht : SatGlobalVertexPlacement.equiv φ (.inr (.inl (endpoints e).2)) =
        target φ (SatClauseOrder.permutation φ) e := rfl
    rw [← hs,← ht]
    simp only [Equiv.apply_eq_iff_eq,Sum.inr.injEq]

theorem route_intersection (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f)
    (q : Point) (he : q ∈ route p e) (hf : q ∈ route p f) :
    (q = point p (endpoints e).1 ∨ q = point p (endpoints e).2) ∧
    (q = point p (endpoints f).1 ∨ q = point p (endpoints f).2) := by
  by_cases hj : e.1 = f.1
  · rcases e with ⟨j,e⟩
    rcases f with ⟨k,f⟩
    dsimp at hj
    subst k
    obtain ⟨v,hv,he,hf⟩ := SatCrossingRetirement.Sides.same_wire_intersection p j e f
      (fun h => hne (Prod.ext rfl h)) q he hf
    constructor
    · exact he.imp (fun h => hv.trans (congrArg (SatCrossingRetirement.Sides.xorPoint p j) h))
        (fun h => hv.trans (congrArg (SatCrossingRetirement.Sides.xorPoint p j) h))
    · exact hf.imp (fun h => hv.trans (congrArg (SatCrossingRetirement.Sides.xorPoint p j) h))
        (fun h => hv.trans (congrArg (SatCrossingRetirement.Sides.xorPoint p j) h))
  · exact False.elim (List.disjoint_left.mp
      (SatCrossingRetirement.Sides.different_wire_sides p e.1 f.1 hj e.2 f.2) he hf)

theorem actual_route_intersection (φ : Formula n m)
    (e f : Edge (SatClauseOrder.permutation φ)) (hne : e ≠ f)
    (q : Point) (he : q ∈ route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ route (SatClauseOrder.permutation φ) f) :
    (q = SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e) ∨
      q = SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (q = SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) f) ∨
      q = SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) f)) := by
  simpa only [source,target,actualPoint_vertex] using
    route_intersection (SatClauseOrder.permutation φ) e f hne q he hf

end GridHardness.SatRetiredSideDrawing
