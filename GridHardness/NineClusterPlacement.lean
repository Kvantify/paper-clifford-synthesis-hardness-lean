/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoClusterAssembly
public import GridHardness.LatticeRouteSeparation

/-!
# Nine Cluster Placement

Place nine-clusters around dilated lattice anchors, with a one-step
horizontal phase chosen from the graph's bipartition. An even dilation
makes every corner have the prescribed checkerboard color, independently
of the parity of the original drawing.
-/

@[expose] public section

namespace GridHardness.NineClusterPlacement
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false

/-- Center the cluster at a dilated anchor, then shift by its color phase. -/
def frame (s : Nat) (p : Point) (χ : Fin 2) : Frame :=
  ⟨true,false,false,((s : Int)*p.1+(χ.val : Int)-1,(s : Int)*p.2-1)⟩

def points (s : Nat) (p : Point) (χ : Fin 2) : Finset Point :=
  TwoClusterAssembly.cluster (frame s p χ)

def corner (s : Nat) (p : Point) (χ : Fin 2) (side : Fin 4) : Point :=
  TwoClusterAssembly.corner (frame s p χ) side

/-- The full translated square, expressed directly in global coordinates. -/
theorem mem_points_iff (s : Nat) (p : Point) (χ : Fin 2) (q : Point) :
    q∈points s p χ ↔
      (s : Int)*p.1+(χ.val : Int)-1≤q.1 ∧ q.1≤(s : Int)*p.1+(χ.val : Int)+1 ∧
      (s : Int)*p.2-1≤q.2 ∧ q.2≤(s : Int)*p.2+1 := by
  rw [points,TwoClusterAssembly.mem_cluster_iff]
  simp only [frame,Frame.unmap,ite_true,sign,Bool.false_eq_true,ite_false]
  omega

/-- A uniform coordinate box independent of the chosen color phase. -/
theorem point_bounds (s : Nat) (p : Point) (χ : Fin 2) (q : Point)
    (hq : q ∈points s p χ) :
    (s : Int)*p.1-1≤q.1 ∧ q.1≤(s : Int)*p.1+2 ∧
      (s : Int)*p.2-1≤q.2 ∧ q.2≤(s : Int)*p.2+1 := by
  have hb := (mem_points_iff s p χ q).mp hq
  have hχ := χ.isLt
  omega

/-- Each cluster lies within radius three of its unshifted scaled anchor. -/
theorem radius (s : Nat) (p : Point) (χ : Fin 2) (q : Point)
    (hq : q ∈points s p χ) :
    IntegerGrid.manhattan (LatticeSubdivision.scale s p) q≤3 := by
  have hb := point_bounds s p χ q hq
  dsimp [IntegerGrid.manhattan,LatticeSubdivision.scale]
  omega

/-- The original scaled anchor itself belongs to either phase of the cluster. -/
theorem anchor_mem (s : Nat) (p : Point) (χ : Fin 2) :
    LatticeSubdivision.scale s p∈points s p χ := by
  rw [mem_points_iff]
  have hχ := χ.isLt
  dsimp [LatticeSubdivision.scale]
  omega

theorem corner_mem (s : Nat) (p : Point) (χ : Fin 2) (side : Fin 4) :
    corner s p χ side∈points s p χ :=
  TwoClusterAssembly.corner_mem (frame s p χ) side

/-- Even dilation removes the original anchor's checkerboard phase. -/
theorem frame_color (s : Nat) (hs : Even s) (p : Point) (χ : Fin 2) (q : Point) :
    color ((frame s p χ).map q)=(q.1+q.2+(χ.val : Int))%2 := by
  have hs' : (s : Int)%2=0 := by
    obtain ⟨k,hk⟩ := hs
    omega
  have hx : ((s : Int)*p.1)%2=0 := by simp [Int.mul_emod,hs']
  have hy : ((s : Int)*p.2)%2=0 := by simp [Int.mul_emod,hs']
  dsimp [frame,Frame.map,place,sign,color]
  omega

/-- All four corner ports have exactly the specified graph color. -/
theorem corner_color (s : Nat) (hs : Even s) (p : Point) (χ : Fin 2) (side : Fin 4) :
    color (corner s p χ side)=(χ.val : Int) := by
  unfold corner TwoClusterAssembly.corner
  rw [frame_color s hs]
  have hχ := χ.isLt
  fin_cases side <;> simp [NineClusterAttachment.corner,NineCluster.port,NineCluster.point] <;>
    omega

/-- Distinct anchors have a scale-sized gap; the two cluster radii use
at most six units of it. -/
theorem points_separated (s : Nat) (p q : Point) (hpq : p ≠q) (χ ψ : Fin 2)
    (u v : Point) (hu : u ∈points s p χ) (hv : v ∈points s q ψ) :
    s-6≤IntegerGrid.manhattan u v := by
  have hp := radius s p χ u hu
  have hq := radius s q ψ v hv
  have hsep := LatticeSubdivision.scale_separation s hpq
  have h1 := IntegerGrid.manhattan_triangle (LatticeSubdivision.scale s p) u
    (LatticeSubdivision.scale s q)
  have h2 := IntegerGrid.manhattan_triangle u v (LatticeSubdivision.scale s q)
  rw [IntegerGrid.manhattan_comm v (LatticeSubdivision.scale s q)] at h2
  omega

/-- At scale eight or larger, distinct clusters cannot overlap. -/
theorem points_disjoint (s : Nat) (hs : 8 ≤s) (p q : Point) (hpq : p ≠q) (χ ψ : Fin 2) :
    Disjoint (points s p χ) (points s q ψ) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  have h := points_separated s p q hpq χ ψ u u hu hv
  simp only [IntegerGrid.manhattan,sub_self,Int.natAbs_zero,Nat.add_zero] at h
  omega

/-- The same margin excludes every unintended unit-grid edge between clusters. -/
theorem points_nonadjacent (s : Nat) (hs : 8 ≤s) (p q : Point) (hpq : p ≠q) (χ ψ : Fin 2)
    (u v : Point) (hu : u ∈points s p χ) (hv : v ∈points s q ψ) :
    ¬lattice.Adj u v := by
  intro ha
  have h := points_separated s p q hpq χ ψ u v hu hv
  change IntegerGrid.manhattan u v=1 at ha
  omega

/-- Phasing and translation preserve the exact nine vertices. -/
theorem points_card (s : Nat) (p : Point) (χ : Fin 2) : (points s p χ).card=9 :=
  TwoClusterAssembly.cluster_card (frame s p χ)

end GridHardness.NineClusterPlacement
