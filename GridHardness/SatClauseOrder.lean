/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClausePlacement
public import GridHardness.CorrectedSatIntervalPermutationGraph
public import Mathlib.Data.Fin.Rev

/-!
# SAT Clause Order

Clause blocks are placed in descending order, while the three literal
slots inside each block keep their order. This makes the directed clause
backbone descend through the gaps between consecutive blocks. The occurrence
permutation here is separate from `SatWireLayout.permutation`.
-/

@[expose] public section

namespace GridHardness.SatClauseOrder
open CliffordSynthesis PlanarSatAssembly PermutationWireLayout
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Reverse clause blocks, preserving each literal's slot within its block. -/
def clauseOrder (m : Nat) : Occurrence m ≃ Fin (3*m) :=
  (Equiv.prodCongr Fin.revPerm (Equiv.refl (Fin 3))).trans (SatWireLayout.clauseRank m)

@[simp] theorem clauseOrder_apply {m : Nat} (o : Occurrence m) :
    clauseOrder m o=SatWireLayout.clauseRank m (Fin.rev o.1,o.2) := rfl

@[simp] theorem clauseOrder_val {m : Nat} (o : Occurrence m) :
    (clauseOrder m o).val=(Fin.rev o.1).val*3+o.2.val :=
  SatWireLayout.clauseRank_val _

def permutation {n m : Nat} (φ : Formula n m) : Equiv.Perm (Fin (3*m)) :=
  (SatWireLayout.variableRank φ).symm.trans (clauseOrder m)

@[simp] theorem permutation_rank {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    permutation φ (SatWireLayout.variableRank φ o)=clauseOrder m o := by
  simp [permutation]

abbrev Point := Int × Int

def base {m : Nat} (c : Fin m) : Int := SatClausePlacement.base (Fin.rev c)

def point {m : Nat} (c : Fin m) (v : Fin 12) : Point :=
  SatClausePlacement.point (Fin.rev c) v

def route {m : Nat} (c : Fin m) (e : Fin 14) : List Point :=
  SatClausePlacement.route (Fin.rev c) e

def InBox {m : Nat} (c : Fin m) (q : Point) : Prop :=
  SatClausePlacement.InBox (Fin.rev c) q

theorem base_eq {m : Nat} (c : Fin m) :
    base c=512*(6*(m:Int)-1-3*c.val) := by
  have hc := c.isLt
  dsimp [base,SatClausePlacement.base]
  omega

theorem point_eq {m : Nat} (c : Fin m) (v : Fin 12) :
    point c v=(-64+(PlanarSatClause.Lattice.point v).1,
      base c+(PlanarSatClause.Lattice.point v).2) :=
  SatClausePlacement.frame_map _ _

theorem point_injective (m : Nat) :
    Function.Injective (fun cv : Fin m × Fin 12 => point cv.1 cv.2) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ h
  have he := SatClausePlacement.point_injective m
    (a₁:=(Fin.rev c,v)) (a₂:=(Fin.rev d,w)) h
  exact Prod.ext (Fin.rev_injective (Prod.mk.inj he).1) (Prod.mk.inj he).2

theorem point_in_box {m : Nat} (c : Fin m) (v : Fin 12) : InBox c (point c v) :=
  SatClausePlacement.point_in_box _ _

theorem route_in_box {m : Nat} (c : Fin m) (e : Fin 14) (q : Point)
    (hq : q ∈route c e) : InBox c q :=
  SatClausePlacement.route_in_box _ _ _ hq

theorem boxes_separated {m : Nat} (c d : Fin m) (hcd : c ≠d) (q r : Point)
    (hq : InBox c q) (hr : InBox d r) : 504≤IntegerGrid.manhattan q r :=
  SatClausePlacement.boxes_separated _ _
    (fun h => hcd (Fin.rev_injective h)) _ _ hq hr

theorem coordinates_bounded {m : Nat} (c : Fin m) (q : Point) (hq : InBox c q) :
    -104≤q.1 ∧ q.1≤-64 ∧ 0≤q.2 ∧ q.2≤3072*m+516 :=
  SatClausePlacement.coordinates_bounded _ _ hq

theorem literal_ports {n m : Nat} (φ : Formula n m) (o : Occurrence m) :
    point o.1 (clauseBottom o.2)=
      (-64,512*high (permutation φ) (SatWireLayout.variableRank φ o)+4) ∧
    point o.1 (clauseTop o.2)=
      (-64,512*high (permutation φ) (SatWireLayout.variableRank φ o)-4) := by
  obtain ⟨hb,ht⟩ := PlanarSatClause.Lattice.literal_ports o.2
  simp only [point_eq,hb,ht,high,permutation_rank,clauseOrder_val]
  dsimp [base,SatClausePlacement.base]
  constructor <;> congr 1 <;> omega

/-- The clause identifier in the source graph remains `c`; only its
geometric block position is reversed. -/
def clauseName {n m : Nat} (c : Fin m) (v : Fin 12) : PlanarSatAssembly.Vertex n m :=
  clause c v

theorem literal_names {n m : Nat} (o : Occurrence m) :
    clauseLinks (n:=n) o=
      [(clauseName o.1 (clauseBottom o.2),xor o 4),
        (xor o 7,clauseName o.1 (clauseTop o.2))] := rfl

/-- The sweep graph for this reversed block order, retaining the original
SAT assembly and its clause identifiers. -/
def graph {n m : Nat} (φ : Formula n m) :=
  CorrectedSatInterval.PermutationGraph.graph φ (permutation φ)

theorem correct {n m : Nat} (φ : Formula n m) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ).adj :=
  CorrectedSatInterval.PermutationGraph.correct φ _

noncomputable def vertex {n m : Nat} (φ : Formula n m) (c : Fin m) (v : Fin 12) :
    (graph φ).Vertex :=
  CorrectedSatInterval.PermutationGraph.liftOriginal φ (permutation φ) (clauseName c v)

theorem vertex_names {n m : Nat} (φ : Formula n m) (c : Fin m) (v : Fin 12) :
    (CorrectedSatInterval.PermutationGraph.number φ (permutation φ) (vertex φ c v)).val=
      (PlanarSatCode.numbering n m).num (clause c v) :=
  CorrectedSatInterval.PermutationGraph.original_names _ _ _

theorem vertex_injective {n m : Nat} (φ : Formula n m) :
    Function.Injective (fun cv : Fin m × Fin 12 => vertex φ cv.1 cv.2) := by
  rintro ⟨c,v⟩ ⟨d,w⟩ h
  have he := CorrectedSatInterval.PermutationGraph.liftOriginal_injective φ
    (permutation φ) h
  simpa only [clauseName,clause,Sum.inr.injEq,Sum.inl.injEq] using he

theorem same_point_iff_same_vertex {n m : Nat} (φ : Formula n m)
    (c d : Fin m) (v w : Fin 12) :
    point c v=point d w ↔ vertex φ c v=vertex φ d w := by
  constructor
  · intro h
    have he := point_injective m (a₁:=(c,v)) (a₂:=(d,w)) h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl
  · intro h
    have he := vertex_injective φ (a₁:=(c,v)) (a₂:=(d,w)) h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl

theorem backbone_ports {m : Nat} (c : Fin m) :
    point c 8=(-64,base c+1028) ∧ point c 1=(-64,base c-4) := by
  obtain ⟨he,hx⟩ := PlanarSatClause.Lattice.backbone_ports
  simp only [point_eq,he,hx]
  constructor <;> congr 1

theorem consecutive_base {m : Nat} (c d : Fin m) (hcd : d.val =c.val +1) :
    base d=base c-1536 := by
  rw [base_eq,base_eq]
  omega

theorem wire_vertex_separation {n m : Nat} (φ : Formula n m) (c : Fin m)
    (q : Point) (hq : InBox c q)
    (v : SatCrossingWireVertices.Vertex (permutation φ)) :
    64≤IntegerGrid.manhattan q (SatCrossingWireVertices.point _ v) := by
  have hw := SatCrossingWireVertices.point_bounds (permutation φ) v
  dsimp [InBox,SatClausePlacement.InBox,IntegerGrid.manhattan] at hq ⊢
  omega

end GridHardness.SatClauseOrder
