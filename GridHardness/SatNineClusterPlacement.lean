/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.NineClusterPlacement
public import GridHardness.SatBipartiteDrawing
public import GridHardness.SatBipartiteCorrectness

/-!
# SAT Nine Cluster Placement

The actual bipartite SAT graph receives separated nine-clusters at
scale sixty-four. Their checkerboard phases agree with the proved graph
coloring, and the color-zero side owns the connecting tentacles.
This module places the cluster bodies; connecting arms remain separate.
-/

@[expose] public section

namespace GridHardness.SatNineClusterPlacement
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatBipartiteDrawing.Vertex
abbrev graph := SatBipartiteDrawing.graph

/-- The graph coloring is the parity of the four-path position. -/
def color (x : SatTy.denote) (v : Vertex x) : Fin 2 :=
  SatBipartiteCorrectness.coloring x v

@[simp] theorem color_val (x : SatTy.denote) (v : Vertex x) :
    (color x v).val=v.2.val%2 := rfl

noncomputable def anchor (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) : Point :=
  LatticeSubdivision.scale 64 (SatBipartiteDrawing.point x hw v)

noncomputable def frame (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) : Frame :=
  NineClusterPlacement.frame 64 (SatBipartiteDrawing.point x hw v) (color x v)

noncomputable def points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : Finset Point :=
  NineClusterPlacement.points 64 (SatBipartiteDrawing.point x hw v) (color x v)

noncomputable def corner (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (side : Fin 4) : Point :=
  NineClusterPlacement.corner 64 (SatBipartiteDrawing.point x hw v) (color x v) side

/-- Every edge has precisely one endpoint on the tentacle-owning side. -/
def ownsTentacles (x : SatTy.denote) (v : Vertex x) : Bool := decide (color x v=0)

theorem corner_color (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (side : Fin 4) :
    OrthogonalTentacle.color (corner x hw v side)=((color x v).val : Int) :=
  NineClusterPlacement.corner_color 64 (by decide) _ _ side

theorem adjacent_colors (x : SatTy.denote) (u v : Vertex x) (huv : (graph x).Adj u v) :
    color x u≠color x v :=
  (SatBipartiteCorrectness.coloring x).valid huv

theorem adjacent_corner_colors (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (u v : Vertex x) (huv : (graph x).Adj u v) (side otherSide : Fin 4) :
    OrthogonalTentacle.color (corner x hw u side)≠
      OrthogonalTentacle.color (corner x hw v otherSide) := by
  rw [corner_color,corner_color]
  intro he
  exact adjacent_colors x u v huv (Fin.ext (by exact_mod_cast he))

theorem opposite_owners (x : SatTy.denote) (u v : Vertex x) (huv : (graph x).Adj u v) :
    ownsTentacles x u≠ownsTentacles x v := by
  have hc := adjacent_colors x u v huv
  unfold ownsTentacles
  generalize color x u=cu at hc ⊢
  generalize color x v=cv at hc ⊢
  fin_cases cu <;> fin_cases cv <;> simp_all

theorem corner_mem (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (side : Fin 4) : corner x hw v side∈points x hw v :=
  NineClusterPlacement.corner_mem 64 _ _ side

theorem anchor_mem (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    anchor x hw v∈points x hw v := NineClusterPlacement.anchor_mem 64 _ _

/-- All cluster vertices lie within three steps of their scaled graph vertex. -/
theorem radius (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (q : Point) (hq : q ∈points x hw v) :
    IntegerGrid.manhattan (anchor x hw v) q≤3 :=
  NineClusterPlacement.radius 64 _ _ q hq

/-- Distinct graph vertices receive clusters with a fifty-eight-step margin. -/
theorem points_separated (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (u v : Vertex x) (huv : u ≠v) (p q : Point)
    (hp : p ∈points x hw u) (hq : q ∈points x hw v) :
    58≤IntegerGrid.manhattan p q :=
  NineClusterPlacement.points_separated 64 _ _
    (fun he => huv (SatBipartiteDrawing.point_injective x hw he)) _ _ p q hp hq

theorem points_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (u v : Vertex x) (huv : u ≠v) : Disjoint (points x hw u) (points x hw v) :=
  NineClusterPlacement.points_disjoint 64 (by decide) _ _
    (fun he => huv (SatBipartiteDrawing.point_injective x hw he)) _ _

theorem points_nonadjacent (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (u v : Vertex x) (huv : u ≠v) (p q : Point)
    (hp : p ∈points x hw u) (hq : q ∈points x hw v) : ¬lattice.Adj p q :=
  NineClusterPlacement.points_nonadjacent 64 (by decide) _ _
    (fun he => huv (SatBipartiteDrawing.point_injective x hw he)) _ _ p q hp hq

theorem points_card (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    (points x hw v).card=9 := NineClusterPlacement.points_card 64 _ _

/-- Explicit linear coordinate bounds for every vertex in every cluster. -/
theorem point_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (q : Point) (hq : q ∈points x hw v) :
    -131265≤q.1 ∧ q.1≤1572864*(x.length : Int)+656578 ∧
      -65729≤q.2 ∧ q.2≤3145728*(x.length : Int)+534721 := by
  have hp := SatBipartitePlacement.point_bounds x hw v
  have hq' := NineClusterPlacement.point_bounds 64 (SatBipartiteDrawing.point x hw v)
    (color x v) q hq
  change -2051≤(SatBipartiteDrawing.point x hw v).1 ∧
    (SatBipartiteDrawing.point x hw v).1≤16*(SatVariableLattice.wireX (3*x.length)+64)+3 ∧
    -1027≤(SatBipartiteDrawing.point x hw v).2 ∧
    (SatBipartiteDrawing.point x hw v).2≤16*(1024*(3*x.length:Int)+522)+3 at hp
  simp only [SatVariableLattice.wireX,Nat.cast_mul,Nat.cast_ofNat] at hp
  norm_num only at hq'
  omega

end GridHardness.SatNineClusterPlacement
