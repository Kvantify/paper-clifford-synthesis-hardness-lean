/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartitePorts
public import GridHardness.DirectedScaledLayout

/-!
# SAT Bipartite Placement

Place the four vertices replacing each actual SAT vertex at scale
sixteen. The internal gadget paths are induced, and distinct gadgets are
separated. Incidence endpoints agree with radius-zero or radius-three
points on their original directed routes. This module does not construct
the external routes or assert a global grid layout.
-/

@[expose] public section

namespace GridHardness.SatBipartitePlacement
open CliffordComplexity PlanarSatAssembly CliffordSynthesis DirectedLocalLayout
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex (x : SatTy.denote) := SatCompleteDrawing.Vertex x × Fin 4
abbrev Point := Int × Int

noncomputable def point (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : Vertex x → Point :=
  DirectedScaledLayout.vertex (SatCompleteDrawing.point x)
    (fun v => (SatBipartitePorts.choose x hw v).direction)
    (fun v => (SatBipartitePorts.choose x hw v).incoming)

theorem point_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    Function.Injective (point x hw) :=
  DirectedScaledLayout.vertex_injective _ _ _ (SatCompleteDrawing.point_injective x hw)

/-- Distinct four-vertex gadgets are separated by at least ten lattice steps. -/
theorem gadgets_separated (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (u v : SatCompleteDrawing.Vertex x) (huv : u ≠v) (i j : Fin 4) :
    10≤IntegerGrid.manhattan (point x hw (u,i)) (point x hw (v,j)) :=
  DirectedScaledLayout.distinct_gadgets_separated _ _
    (fun h => huv (SatCompleteDrawing.point_injective x hw h)) _ _ _ _ _ _

/-- Among the displayed vertices, precisely the internal gadget edges
are adjacent in the integer lattice. -/
theorem adjacency_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (u v : Vertex x) :
    IntegerGrid.manhattan (point x hw u) (point x hw v)=1 ↔
      u.1=v.1 ∧ (u.2.val+1=v.2.val ∨ v.2.val+1=u.2.val) :=
  DirectedScaledLayout.vertex_adjacency_iff _ _ _ (SatCompleteDrawing.point_injective x hw) u v

theorem local_adjacency (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : SatCompleteDrawing.Vertex x) (i j : Fin 4) :
    IntegerGrid.manhattan (point x hw (v,i)) (point x hw (v,j))=1 ↔
      i.val+1=j.val ∨ j.val+1=i.val := by
  simpa only [true_and] using adjacency_iff x hw (v,i) (v,j)

/-- All gadget vertices remain in a rectangle linear in the input length. -/
theorem point_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    -2051≤(point x hw v).1 ∧
    (point x hw v).1≤16*(SatVariableLattice.wireX (3*x.length)+64)+3 ∧
    -1027≤(point x hw v).2 ∧
    (point x hw v).2≤16*(1024*(3*x.length:Int)+522)+3 := by
  have hb := SatGlobalVertexPlacement.actualPoint_bounds (finiteFormula x) v.1
  have hp := DirectedScaledLayout.place_bounds (SatCompleteDrawing.point x v.1)
    (SatBipartitePorts.choose x hw v.1).direction
    (SatBipartitePorts.choose x hw v.1).incoming v.2
  change 16*(SatCompleteDrawing.point x v.1).1-3≤(point x hw v).1 ∧
    (point x hw v).1≤16*(SatCompleteDrawing.point x v.1).1+3 ∧
    16*(SatCompleteDrawing.point x v.1).2-3≤(point x hw v).2 ∧
    (point x hw v).2≤16*(SatCompleteDrawing.point x v.1).2+3 at hp
  change -128≤(SatCompleteDrawing.point x v.1).1 ∧
    (SatCompleteDrawing.point x v.1).1≤SatVariableLattice.wireX (3*x.length)+64 ∧
    -64≤(SatCompleteDrawing.point x v.1).2 ∧
    (SatCompleteDrawing.point x v.1).2≤1024*(3*x.length:Int)+522 at hb
  omega

/-- Incoming arcs attach to index zero and outgoing arcs to index three. -/
def portIndex (incoming : Bool) : Fin 4 := if incoming then 0 else 3

/-- The singleton side is attached at radius three, and the other side
at the original anchor. -/
noncomputable def portRadius (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : SatCompleteDrawing.Vertex x) (incoming : Bool) : Nat :=
  if incoming=(SatBipartitePorts.choose x hw v).incoming then 3 else 0

theorem portRadius_cases (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : SatCompleteDrawing.Vertex x) (b : Bool) :
    portRadius x hw v b=0 ∨ portRadius x hw v b=3 := by
  unfold portRadius
  split_ifs <;> simp

theorem portRadius_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : SatCompleteDrawing.Vertex x) (b : Bool) : portRadius x hw v b≤3 := by
  rcases portRadius_cases x hw v b with h | h <;> omega

private theorem local_port (d : Fin 4) (incoming b : Bool) :
    vertexPoint d incoming (portIndex b)=ray d (if b=incoming then 3 else 0) := by
  cases incoming <;> cases b <;> simp [vertexPoint,portIndex]

/-- The endpoint selected in the replacement gadget lies on the same
cardinal ray as the original directed incidence, at its chosen radius. -/
theorem port_point (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : SatCompleteDrawing.Arc x) (b : Bool) :
    point x hw (SatCompleteDrawing.endpointVertex x a b,portIndex b)=
      ((DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).1 +
        (ray (SatCompleteDrawing.direction x a b)
          (portRadius x hw (SatCompleteDrawing.endpointVertex x a b) b)).1,
       (DirectedScaledLayout.anchor
          (SatCompleteDrawing.point x (SatCompleteDrawing.endpointVertex x a b))).2 +
        (ray (SatCompleteDrawing.direction x a b)
          (portRadius x hw (SatCompleteDrawing.endpointVertex x a b) b)).2) := by
  let v := SatCompleteDrawing.endpointVertex x a b
  let c := SatBipartitePorts.choose x hw v
  have hi := c.direction_iff (⟨(a,b),rfl⟩ : SatCompleteDrawing.Incidence x v)
  change SatCompleteDrawing.direction x a b=c.direction ↔ b=c.incoming at hi
  change ((DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).1 +
      (vertexPoint c.direction c.incoming (portIndex b)).1,
    (DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).2 +
      (vertexPoint c.direction c.incoming (portIndex b)).2)=_
  rw [local_port]
  change _=((DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).1+
      (ray (SatCompleteDrawing.direction x a b) (if b=c.incoming then 3 else 0)).1,
    (DirectedScaledLayout.anchor (SatCompleteDrawing.point x v)).2+
      (ray (SatCompleteDrawing.direction x a b) (if b=c.incoming then 3 else 0)).2)
  by_cases hb : b=c.incoming
  · rw [ite_eq_left hb,hi.mpr hb]
  · simp only [ite_eq_right hb,ray_zero]

end GridHardness.SatBipartitePlacement
