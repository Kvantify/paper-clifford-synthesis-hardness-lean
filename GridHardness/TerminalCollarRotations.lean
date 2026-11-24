/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarExtension
public import GridHardness.TwoClusterTransform
public import GridHardness.ClusterStar

/-!
# Terminal Collar Rotations

Four copies of the terminal collar around a single odd nine-cluster.
Rotations are about the actual cluster center `(1,0)`, so the finite
pointsets are pairwise separated and all four singleton docks use the
same target cluster. The entering rungs have explicitly recorded offsets;
matching these to a globally chosen corridor remains a separate task.
-/

@[expose] public section

namespace GridHardness.TerminalCollarRotations
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open TerminalCollar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

/-- Counterclockwise quarter-turns about the odd cluster center `(1,0)`.
The index also names the cluster side: left, bottom, right, top. -/
def rotation : Fin 4 → Frame :=
  ![⟨true,false,false,(0,0)⟩,⟨false,false,true,(1,-1)⟩,
    ⟨true,true,true,(2,0)⟩,⟨false,true,false,(1,1)⟩]

def points (s : Fin 4) : Finset Point := collarPoints.image (rotation s).map

def entry (s : Fin 4) (r : Fin 2) : Point :=
  (rotation s).map (-8,(r.val : Int))

def tip (s : Fin 4) (r : Fin 2) : Point :=
  (rotation s).map (-1,-1-(r.val : Int))

theorem card (s : Fin 4) : (points s).card = 32 := by
  rw [points,Finset.card_image_of_injective _ (rotation s).injective,collar_card]

/-- The collar fits inside a radius-sixteen coordinate square about
the original route anchor, despite the one-unit cluster phase shift. -/
theorem bounds : ∀ s : Fin 4, ∀ p ∈ points s,
    -16 ≤ p.1 ∧ p.1 ≤ 16 ∧ -16 ≤ p.2 ∧ p.2 ≤ 16 := by
  decide

/-- All four finite collar interiors remain at least three grid steps
apart, including the detours on adjacent sides. -/
theorem distance : ∀ s t : Fin 4, s ≠ t → ∀ p ∈ points s, ∀ q ∈ points t,
    3 ≤ IntegerGrid.manhattan p q := by
  decide

theorem apart (s t : Fin 4) (hst : s ≠ t) : ClusterStar.Apart (points s) (points t) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have hd := distance s t hst p hp p hq
    simp [IntegerGrid.manhattan] at hd
  · intro p hp q hq ha
    have hd := distance s t hst p hp q hq
    change IntegerGrid.manhattan p q = 1 at ha
    omega

/-- All rotations preserve exactly the same placed nine-point cluster. -/
theorem cluster_fixed (s : Fin 4) :
    (TwoClusterAssembly.cluster clusterFrame).image (rotation s).map =
      TwoClusterAssembly.cluster clusterFrame := by
  fin_cases s <;> decide

theorem corner_rotated (s : Fin 4) :
    (rotation s).map (TwoClusterAssembly.corner clusterFrame 0) =
      TwoClusterAssembly.corner clusterFrame s := by
  fin_cases s <;> rfl

theorem entry_coordinates (s : Fin 4) (r : Fin 2) :
    entry s r = ![(-8,(r.val : Int)),(1-(r.val : Int),-9),
      (10,-(r.val : Int)),(1+(r.val : Int),9)] s := by
  fin_cases s <;> simp [entry,rotation,Frame.map,place,sign,sub_eq_add_neg]

theorem tip_coordinates (s : Fin 4) (r : Fin 2) :
    tip s r = ![(-1,-1-(r.val : Int)),(2+(r.val : Int),-2),
      (3,1+(r.val : Int)),(-(r.val : Int),2)] s := by
  fin_cases s <;> simp [tip,rotation,Frame.map,place,sign,sub_eq_add_neg]
  all_goals omega

theorem entry_mem (s : Fin 4) (r : Fin 2) : entry s r ∈ points s := by
  apply Finset.mem_image.mpr
  refine ⟨(-8,(r.val : Int)),north_subset_collar ?_,rfl⟩
  rw [mem_north]
  have hr := r.isLt
  omega

theorem tip_mem (s : Fin 4) (r : Fin 2) : tip s r ∈ points s := by
  apply Finset.mem_image.mpr
  refine ⟨(-1,-1-(r.val : Int)),terminal_subset_collar ?_,rfl⟩
  rw [mem_terminal]
  have hr := r.isLt
  omega

theorem cluster_disjoint (s : Fin 4) :
    Disjoint (TwoClusterAssembly.cluster clusterFrame) (points s) := by
  rw [points,← cluster_fixed s]
  apply (Finset.disjoint_image (rotation s).injective).mpr
  apply Finset.disjoint_left.mpr
  intro p hp hq
  apply Finset.disjoint_left.mp (TerminalCollar.cluster_disjoint 0) hp
  rw [points_union]
  exact Finset.mem_union_right _ hq

/-- Every rotated finite collar has exactly one induced boundary edge
to the common target cluster, ending at the stated lane-zero tip. -/
theorem boundary_singleton (s : Fin 4) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster clusterFrame) (points s) =
      {(TwoClusterAssembly.corner clusterFrame s,tip s 0)} := by
  have hb : TwoClusterAssembly.boundary (TwoClusterAssembly.cluster clusterFrame) collarPoints =
      {(TwoClusterAssembly.corner clusterFrame 0,(-1,-1))} := by
    decide
  unfold points
  rw [← cluster_fixed s,TwoClusterAssembly.boundary_transform,hb,Finset.image_singleton]
  rw [corner_rotated]
  rfl

/-- The complete earlier drawing may be rotated with the same frame.
This preserves the finite geometric validity certificate. -/
theorem rotated_append_valid (s : Fin 4) (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8,(r.val : Int)))) (hf : Frontier d) :
    (Drawing.transform (rotation s) (append d)).Valid :=
  Drawing.transform_valid _ _ (append_valid d hv ht hf)

theorem rotated_append_tip (s : Fin 4) (d : Drawing) (r : Fin 2) :
    (Drawing.transform (rotation s) (append d)).tip r = tip s r := by
  rw [Drawing.transform_tip,append_tip]
  rfl

/-- For any cleared preceding drawing, the transported singleton
boundary attaches to the correct side of the unchanged target cluster. -/
theorem rotated_append_boundary (s : Fin 4) (d : Drawing) (hv : d.Valid)
    (ht : Aligned d.tip (fun r : Fin 2 => (-8,(r.val : Int)))) (hf : Frontier d) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster clusterFrame)
      (Drawing.transform (rotation s) (append d)).points =
        {(TwoClusterAssembly.corner clusterFrame s,tip s 0)} := by
  rw [Drawing.transform_points,← cluster_fixed s,TwoClusterAssembly.boundary_transform,
    append_boundary_singleton d hv ht hf,Finset.image_singleton,corner_rotated,append_tip]
  rfl

end GridHardness.TerminalCollarRotations
