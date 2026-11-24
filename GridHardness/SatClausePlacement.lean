/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatClauseLattice
public import GridHardness.CorrectedSatIntervalWirePlacement

/-!
# SAT Clause Placement

Place clause bodies to the left of the occurrence-wire rectangle.
The six literal ports match the clause-order heights. This module covers
vertices and internal edges. `SatClauseDrawing` supplies the backbone and
`SatClauseWireLattice` supplies the links to occurrence wires.
-/

@[expose] public section

namespace GridHardness.SatClausePlacement
open CliffordSynthesis SignedTentacle PermutationWireLayout
open PlanarSatAssembly CorrectedSatInterval CorrectedSatInterval.GlobalNumbering
set_option autoImplicit false

abbrev Point := Int × Int

def base {m : Nat} (c : Fin m) : Int := 512*((3*m:Int)+2+3*c.val)

def frame {m : Nat} (c : Fin m) : Frame :=
  ⟨true,false,false,(-64,base c)⟩

theorem frame_map {m : Nat} (c : Fin m) (q : Point) :
    (frame c).map q=(-64+q.1,base c+q.2) := by
  simp [frame,Frame.map,OrthogonalTentacle.place,sign]

def point {m : Nat} (c : Fin m) (v : Fin 12) : Point :=
  (frame c).map (PlanarSatClause.Lattice.point v)

def route {m : Nat} (c : Fin m) (e : Fin 14) : List Point :=
  (PlanarSatClause.Lattice.route e).map (frame c).map

def InBox {m : Nat} (c : Fin m) (q : Point) : Prop :=
  -104≤q.1 ∧ q.1≤-64 ∧ base c-4≤q.2 ∧ q.2≤base c+1028

theorem map_in_box {m : Nat} (c : Fin m) (q : Point)
    (hq : PlanarSatClause.Lattice.InBox q) : InBox c ((frame c).map q) := by
  rw [frame_map]
  dsimp [InBox,PlanarSatClause.Lattice.InBox] at hq ⊢
  omega

theorem point_in_box {m : Nat} (c : Fin m) (v : Fin 12) : InBox c (point c v) :=
  map_in_box c _ (PlanarSatClause.Lattice.point_in_box v)

theorem route_in_box {m : Nat} (c : Fin m) (e : Fin 14) (q : Point)
    (hq : q ∈route c e) : InBox c q := by
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
  exact map_in_box c z (PlanarSatClause.Lattice.route_in_box e z hz)

theorem boxes_separated {m : Nat} (c d : Fin m) (hcd : c ≠d) (q r : Point)
    (hq : InBox c q) (hr : InBox d r) : 504≤IntegerGrid.manhattan q r := by
  have hc : c.val≠d.val := fun h => hcd (Fin.ext h)
  dsimp [InBox,base,IntegerGrid.manhattan] at hq hr ⊢
  omega

theorem point_injective (m : Nat) :
    Function.Injective (fun cv : Fin m × Fin 12 => point cv.1 cv.2) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ h
  change point c v=point d w at h
  by_cases hc : c=d
  · subst d
    exact Prod.ext rfl (PlanarSatClause.Lattice.point_injective ((frame c).injective h))
  · have hs := boxes_separated c d hc _ _ (point_in_box c v) (point_in_box d w)
    rw [h] at hs
    simp [IntegerGrid.manhattan] at hs

theorem coordinates_bounded {m : Nat} (c : Fin m) (q : Point) (hq : InBox c q) :
    -104≤q.1 ∧ q.1≤-64 ∧ 0≤q.2 ∧ q.2≤3072*m+516 := by
  have hc := c.isLt
  dsimp [InBox,base] at hq
  omega

theorem route_certificate {m : Nat} (c : Fin m) (e : Fin 14) :
    (route c e).head?=some (point c (PlanarSatClause.Lattice.edge e).1) ∧
    (route c e).getLast?=some (point c (PlanarSatClause.Lattice.edge e).2) ∧
    (route c e).Nodup ∧ (route c e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2≤(route c e).length ∧ (route c e).length≤1073 := by
  obtain ⟨hh,ht⟩ := PlanarSatClause.Lattice.route_endpoints e
  obtain ⟨hn,hs⟩ := PlanarSatClause.Lattice.route_simple e
  obtain ⟨hl,hu⟩ := PlanarSatClause.Lattice.route_length_bound e
  refine ⟨?_,?_,hn.map (frame c).injective,?_,?_,?_⟩
  · simp only [route,List.head?_map,hh,Option.map_some,point]
  · simp only [route,List.getLast?_map,ht,Option.map_some,point]
  · apply List.isChain_map_of_isChain _ _ hs
    intro a b hab
    change IntegerGrid.manhattan _ _=1
    rw [(frame c).distance]
    exact hab
  · simpa only [route,List.length_map] using hl
  · simpa only [route,List.length_map] using hu

theorem different_clauses_disjoint {m : Nat} (c d : Fin m) (hcd : c ≠d)
    (e f : Fin 14) : (route c e).Disjoint (route d f) := by
  apply List.disjoint_left.mpr
  intro q hq hr
  have hs := boxes_separated c d hcd q q (route_in_box c e q hq) (route_in_box d f q hr)
  simp [IntegerGrid.manhattan] at hs

theorem route_vertex_clear {m : Nat} (c : Fin m) (e : Fin 14) (v : Fin 12) :
    point c v∈route c e ↔
      v=(PlanarSatClause.Lattice.edge e).1 ∨ v=(PlanarSatClause.Lattice.edge e).2 := by
  change (frame c).map (PlanarSatClause.Lattice.point v)∈
    (PlanarSatClause.Lattice.route e).map (frame c).map ↔ _
  rw [List.mem_map_of_injective (frame c).injective]
  exact PlanarSatClause.Lattice.route_vertex_clear e v

theorem route_intersection {m : Nat} (c : Fin m) (e f : Fin 14) (hef : e ≠f)
    (q : Point) (he : q ∈route c e) (hf : q ∈route c f) :
    (q=point c (PlanarSatClause.Lattice.edge e).1 ∨
      q=point c (PlanarSatClause.Lattice.edge e).2) ∧
    (q=point c (PlanarSatClause.Lattice.edge f).1 ∨
      q=point c (PlanarSatClause.Lattice.edge f).2) := by
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp he
  have hz' := (List.mem_map_of_injective (frame c).injective).mp hf
  have hh := PlanarSatClause.Lattice.route_intersection e f hef z hz hz'
  exact ⟨hh.1.imp (congrArg (frame c).map) (congrArg (frame c).map),
    hh.2.imp (congrArg (frame c).map) (congrArg (frame c).map)⟩

/-- The literal ports have exactly the heights used by the actual wire
permutation, independently of which variable occurs in the slot. -/
theorem literal_ports {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    point o.1 (clauseBottom o.2)=
      (-64,512*high (SatWireLayout.permutation φ) (SatWireLayout.variableRank φ o)+4) ∧
    point o.1 (clauseTop o.2)=
      (-64,512*high (SatWireLayout.permutation φ) (SatWireLayout.variableRank φ o)-4) := by
  obtain ⟨hb,ht⟩ := PlanarSatClause.Lattice.literal_ports o.2
  simp only [point,hb,ht,frame_map,high,SatWireLayout.permutation_rank,
    SatWireLayout.clauseRank_val]
  dsimp [base]
  constructor <;> congr 1 <;> omega

theorem wire_vertex_separation {n m : Nat} (φ : Formula n m) (c : Fin m)
    (q : Point) (hq : InBox c q)
    (v : SatCrossingWireVertices.Vertex (SatWireLayout.permutation φ)) :
    64≤IntegerGrid.manhattan q (SatCrossingWireVertices.point _ v) := by
  have hw := SatCrossingWireVertices.point_bounds (SatWireLayout.permutation φ) v
  dsimp [InBox,IntegerGrid.manhattan] at hq ⊢
  omega

noncomputable def vertex (x : CliffordComplexity.SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    (actualGraph x).Vertex := formulaLift (finiteFormula x) (clause c v)

theorem vertex_names (x : CliffordComplexity.SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    actualDecomposition x (vertex x c v)=.inl (clause c v) :=
  actualDecomposition_old x (clause c v)

theorem vertex_injective (x : CliffordComplexity.SatTy.denote) :
    Function.Injective (fun cv : Fin x.length × Fin 12 => vertex x cv.1 cv.2) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ h
  change vertex x c v=vertex x d w at h
  have hn := congrArg (actualDecomposition x) h
  rw [vertex_names,vertex_names] at hn
  simpa only [clause,Sum.inl.injEq,Sum.inr.injEq] using hn

theorem vertex_ne_wire (x : CliffordComplexity.SatTy.denote) (c : Fin x.length) (v : Fin 12)
    (w : WirePlacement.WireVertex x) : vertex x c v≠WirePlacement.vertex x w := by
  intro h
  have hn := congrArg (actualDecomposition x) h
  rw [vertex_names,WirePlacement.vertex,Equiv.apply_symm_apply] at hn
  cases w with
  | inl j => cases hn
  | inr z => cases hn

end GridHardness.SatClausePlacement
