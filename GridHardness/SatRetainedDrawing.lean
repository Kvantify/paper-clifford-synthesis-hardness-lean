/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalRetainedEdges
public import GridHardness.SatGlobalVertexPlacement
public import GridHardness.SatCrossingHorizontalEdgeClearance
public import GridHardness.SatCrossingRetirementSides

/-!
# SAT Retained Drawing

Retained internal crossing edges as actual final-graph arcs. Each
index contains an active crossing and a local edge whose endpoints survive
section-zero removal. Same-cell adjacency is exact. The routes are simple,
bounded, mutually compatible, and exclude every unrelated final vertex.
Crossing connectors and retired-wire arcs are separate families.
-/

@[expose] public section

namespace GridHardness.SatRetainedDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev LocalEdge := {e : Fin 66 // SatCrossingHorizontal.RetainedEdge e}
abbrev Vertex {N : Nat} (p : Equiv.Perm (Fin N)) :=
  WireCrossingSchedule.Cell p × SatCrossingHorizontal.RetainedVertex
abbrev Edge {N : Nat} (p : Equiv.Perm (Fin N)) :=
  WireCrossingSchedule.Cell p × LocalEdge

theorem local_edge_count : Fintype.card LocalEdge = 54 := by decide +kernel

def localEndpoints (e : LocalEdge) :
    SatCrossingHorizontal.RetainedVertex × SatCrossingHorizontal.RetainedVertex :=
  (⟨(XorLine.Lattice.edge e.val).1,e.property.1⟩,
    ⟨(XorLine.Lattice.edge e.val).2,e.property.2⟩)

def endpoints {N : Nat} {p : Equiv.Perm (Fin N)} (e : Edge p) : Vertex p × Vertex p :=
  ((e.1,(localEndpoints e.2).1),(e.1,(localEndpoints e.2).2))

def point {N : Nat} (p : Equiv.Perm (Fin N)) (v : Vertex p) : Point :=
  SatCrossingLattice.point p v.1.val v.2.val

def route {N : Nat} (p : Equiv.Perm (Fin N)) (e : Edge p) : List Point :=
  SatCrossingLattice.route p e.1.val e.2.val

variable {N n m : Nat}

noncomputable def vertex (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (v : Vertex p) :
    (PermutationGraph.graph φ p).Vertex :=
  PermutationWirePlacement.fresh φ p v.1 v.2

noncomputable def source (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := vertex φ p (endpoints e).1

noncomputable def target (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).Vertex := vertex φ p (endpoints e).2

theorem local_adj_iff (u v : SatCrossingHorizontal.RetainedVertex) :
    XorLine.Adj 4 u.val v.val ↔ ∃ e : LocalEdge, localEndpoints e = (u,v) := by
  rw [XorLine.Lattice.adj_iff_edge]
  constructor
  · rintro ⟨i,hi⟩
    have hr : SatCrossingHorizontal.RetainedEdge i := by
      simpa [SatCrossingHorizontal.RetainedEdge,hi] using And.intro u.property v.property
    refine ⟨⟨i,hr⟩,?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hi
    · exact congrArg Prod.snd hi
  · rintro ⟨e,he⟩
    exact ⟨e.val,congrArg (fun z => (z.1.val,z.2.val)) he⟩

/-- Exact adjacency of the subgraph induced by the forty retained
vertices of one actual crossing; no claim about cross-cell edges is made. -/
theorem same_cell_adj_iff (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (c : WireCrossingSchedule.Cell p) (u v : SatCrossingHorizontal.RetainedVertex) :
    (PermutationGraph.graph φ p).adj (vertex φ p (c,u)) (vertex φ p (c,v)) ↔
      ∃ e : LocalEdge, localEndpoints e = (u,v) := by
  rw [vertex,vertex,RetainedEdges.permutation_adj_iff,local_adj_iff]

theorem edge_is_arc (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) (e : Edge p) :
    (PermutationGraph.graph φ p).adj (source φ p e) (target φ p e) :=
  RetainedEdges.permutation_edge φ p e.1 (localEndpoints e.2).1 (localEndpoints e.2).2
    (XorLine.Lattice.edge_adj e.2.val)

theorem actualPoint_vertex (φ : Formula n m) (v : Vertex (SatClauseOrder.permutation φ)) :
    SatGlobalVertexPlacement.actualPoint φ (vertex φ (SatClauseOrder.permutation φ) v) =
      point (SatClauseOrder.permutation φ) v := by
  rw [vertex,← PermutationWirePlacement.vertex_fresh,SatGlobalVertexPlacement.actualPoint_wire]
  rfl

theorem route_certificate (p : Equiv.Perm (Fin N)) (e : Edge p) :
    (route p e).head? = some (point p (endpoints e).1) ∧
    (route p e).getLast? = some (point p (endpoints e).2) ∧
    (route p e).Nodup ∧ (route p e).IsChain XorLine.Lattice.UnitStep ∧
    2 ≤ (route p e).length ∧ (route p e).length ≤ 17 :=
  SatCrossingLattice.route_certificate p e.1.val e.2.val

-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- The geometric proof unfolds the coordinates of the constructed routes.
private theorem local_length_lower : ∀ i : Fin 66, 3 ≤ (XorLine.Lattice.edgeRoute i).length := by
  decide +kernel

theorem route_length_lower (p : Equiv.Perm (Fin N)) (e : Edge p) :
    3 ≤ (route p e).length := by
  simpa only [route,SatCrossingLattice.route,List.length_map] using local_length_lower e.2.val

theorem actual_route_certificate (φ : Formula n m) (e : Edge (SatClauseOrder.permutation φ)) :
    (route (SatClauseOrder.permutation φ) e).head? =
        some (SatGlobalVertexPlacement.actualPoint φ (source φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).getLast? =
        some (SatGlobalVertexPlacement.actualPoint φ (target φ (SatClauseOrder.permutation φ) e)) ∧
    (route (SatClauseOrder.permutation φ) e).Nodup ∧
    (route (SatClauseOrder.permutation φ) e).IsChain XorLine.Lattice.UnitStep ∧
    2 ≤ (route (SatClauseOrder.permutation φ) e).length ∧
    (route (SatClauseOrder.permutation φ) e).length ≤ 17 := by
  simpa only [source,target,actualPoint_vertex] using route_certificate (SatClauseOrder.permutation φ) e

theorem route_bounds (p : Equiv.Perm (Fin N)) (e : Edge p) (q : Point)
    (hq : q ∈ route p e) :
    0 ≤ q.1 ∧ q.1 ≤ 512*N+65 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1024*N+522 :=
  SatCrossingLattice.coordinates_bounded p e.1.val q
    (SatCrossingLattice.route_in_box p e.1.val e.2.val q hq)

theorem placed_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p) (v : Vertex p) :
    point p v ∈ route p e ↔ v = (endpoints e).1 ∨ v = (endpoints e).2 := by
  by_cases hc : v.1 = e.1
  · rcases e with ⟨c,e⟩
    rcases v with ⟨d,v⟩
    dsimp at hc
    subst d
    change SatCrossingLattice.point p c.val v.val ∈ SatCrossingLattice.route p c.val e.val ↔ _
    rw [SatCrossingLattice.route_vertex_clear]
    constructor
    · intro h
      exact h.imp (fun h => Prod.ext rfl (Subtype.ext h))
        (fun h => Prod.ext rfl (Subtype.ext h))
    · rintro (h | h)
      · exact Or.inl (congrArg (fun z : Vertex p => z.2.val) h)
      · exact Or.inr (congrArg (fun z : Vertex p => z.2.val) h)
  · constructor
    · intro h
      have hs := SatCrossingLattice.boxes_separated p v.1.val e.1.val
        (fun h => hc (Subtype.ext h)) _ _
        (SatCrossingLattice.point_in_box p v.1.val v.2.val)
        (SatCrossingLattice.route_in_box p e.1.val e.2.val _ h)
      simp [point,IntegerGrid.manhattan] at hs
    · rintro (h | h) <;> exact False.elim (hc (congrArg Prod.fst h))

private theorem side_incident : ∀ v : Fin 8, ∃ e : Fin 6,
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).1 ∨
    v = (XorGadget.arc (SatCrossingRetirement.sideArc e)).2 := by decide +kernel

theorem wire_vertex_clear (p : Equiv.Perm (Fin N)) (e : Edge p)
    (v : SatCrossingWireVertices.Vertex p) :
    SatCrossingWireVertices.point p v ∈ route p e ↔
      v = .inr (endpoints e).1 ∨ v = .inr (endpoints e).2 := by
  cases v with
  | inl iv =>
    simp only [reduceCtorEq,or_self,iff_false]
    intro h
    obtain ⟨i,v⟩ := iv
    obtain ⟨s,hs⟩ := side_incident v
    have hm := (SatCrossingRetirement.Sides.route_vertex_clear p i s v).mpr hs
    exact List.disjoint_left.mp
      (SatCrossingRetirement.Sides.retained_routes_disjoint p i s e.1.val e.2.val
        e.2.property.1 e.2.property.2) hm h
  | inr v =>
    simpa only [SatCrossingWireVertices.point,point,Sum.inr.injEq] using placed_vertex_clear p e v

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

/-- Retained internal routes contain no other actual final graph vertex,
including retired XOR vertices and every body family. -/
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

theorem route_intersection (p : Equiv.Perm (Fin N)) (e f : Edge p) (hne : e ≠ f)
    (q : Point) (he : q ∈ route p e) (hf : q ∈ route p f) :
    (q = point p (endpoints e).1 ∨ q = point p (endpoints e).2) ∧
    (q = point p (endpoints f).1 ∨ q = point p (endpoints f).2) := by
  by_cases hc : e.1 = f.1
  · rcases e with ⟨c,e⟩
    rcases f with ⟨d,f⟩
    dsimp at hc
    subst d
    have hef : e.val ≠ f.val := fun h => hne (Prod.ext rfl (Subtype.ext h))
    obtain ⟨u,hu,hq⟩ := List.mem_map.mp he
    have hv : u ∈ XorLine.Lattice.edgeRoute f.val := by
      rw [← hq] at hf
      exact (List.mem_map_of_injective (SatCrossingLattice.frame p c.val).injective).mp hf
    have h := XorLine.Lattice.intersection_certificate e.val f.val hef u hu hv
    constructor
    · exact h.1.imp (fun h => hq.symm.trans (congrArg (SatCrossingLattice.frame p c.val).map h))
        (fun h => hq.symm.trans (congrArg (SatCrossingLattice.frame p c.val).map h))
    · exact h.2.imp (fun h => hq.symm.trans (congrArg (SatCrossingLattice.frame p c.val).map h))
        (fun h => hq.symm.trans (congrArg (SatCrossingLattice.frame p c.val).map h))
  · exact False.elim (List.disjoint_left.mp
      (SatCrossingLattice.distinct_cell_routes_disjoint p e.1.val f.1.val
        (fun h => hc (Subtype.ext h)) e.2.val f.2.val) he hf)

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

end GridHardness.SatRetainedDrawing
