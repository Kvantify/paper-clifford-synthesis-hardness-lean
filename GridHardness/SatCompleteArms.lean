/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteLocalDrawing
public import GridHardness.SatCompleteTentacleSeparation
public import GridHardness.SatOwnerIncidences
public import GridHardness.TerminalCollarOwner

/-!
# SAT Complete Arms

The actual completed edge tentacles fill the three incidence slots at
each owning vertex. Their validity, distinct sides, geometric separation,
and designated output ports satisfy the existing star interface.
-/

@[expose] public section

namespace GridHardness.SatCompleteArms
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev Vertex := SatDockCorridors.Vertex
abbrev Edge := SatDockCorridors.Edge
abbrev Incidence := SatBipartiteDirections.Incidence

noncomputable def localDrawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) : Drawing :=
  Drawing.transform (SatNineClusterPlacement.frame x hw v).inverse
    (SatCompleteTentacles.drawing x hw e)

noncomputable def arms (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : GridAssembly.Arms := fun k =>
  (SatClusterStubs.atSlot x v k).map (fun i =>
    (SatClusterStubs.side x hw v i,localDrawing x hw v (SatOwnerIncidences.edge x v i)))

@[simp] theorem localDrawing_placed (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) :
    Drawing.transform (SatNineClusterPlacement.frame x hw v) (localDrawing x hw v e)=
      SatCompleteTentacles.drawing x hw e := Drawing.transform_inverse _ _

theorem localDrawing_points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) :
    (localDrawing x hw v e).points.image (SatNineClusterPlacement.frame x hw v).map =
      (SatCompleteTentacles.drawing x hw e).points := by
  rw [← Drawing.transform_points,localDrawing_placed]

theorem localDrawing_tip (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) (r : Fin 2) :
    (SatNineClusterPlacement.frame x hw v).map ((localDrawing x hw v e).tip r)=
      (SatCompleteTentacles.drawing x hw e).tip r := by
  rw [← Drawing.transform_tip,localDrawing_placed]

theorem localDrawing_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) : (localDrawing x hw v e).Valid :=
  Drawing.transform_valid _ _ (SatCompleteTentacles.valid x hw e)

theorem localDrawing_docked (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    NineClusterAttachment.Docked true (SatClusterStubs.side x hw v i)
      (localDrawing x hw v (SatOwnerIncidences.edge x v i)) := by
  have h := SatCompleteTentacles.localDrawing_docked x hw (SatOwnerIncidences.edge x v i)
  change NineClusterAttachment.Docked true _ (Drawing.transform
    (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x (SatOwnerIncidences.edge x v i))).inverse
      (SatCompleteTentacles.drawing x hw (SatOwnerIncidences.edge x v i))) at h
  rw [SatOwnerIncidences.owner_of_incidence x v hv i,SatOwnerIncidences.side_eq x hw v hv i] at h
  exact h

theorem localDrawing_apart (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e f : Edge x) (hef : e ≠f) :
    ClusterStar.Apart (localDrawing x hw v e).points (localDrawing x hw v f).points := by
  have hd (p q : Point) (hp : p∈(localDrawing x hw v e).points)
      (hq : q∈(localDrawing x hw v f).points) : 2≤IntegerGrid.manhattan p q := by
    have hp' : (SatNineClusterPlacement.frame x hw v).map p∈(SatCompleteTentacles.drawing x hw e).points := by
      rw [← localDrawing_points x hw v e]
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    have hq' : (SatNineClusterPlacement.frame x hw v).map q∈(SatCompleteTentacles.drawing x hw f).points := by
      rw [← localDrawing_points x hw v f]
      exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
    simpa only [Frame.distance] using SatCompleteTentacles.pairwise_distance x hw e f hef _ _ hp' hq'
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := hd p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq ha
    have h := hd p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega

@[simp] theorem arms_slot (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (i : Incidence x v) :
    arms x hw v (SatClusterStubs.slot x v i)=
      some (SatClusterStubs.side x hw v i,localDrawing x hw v (SatOwnerIncidences.edge x v i)) := by
  simp [arms]

theorem arms_eq_some_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (k : Fin 3) (s : Fin 4) (d : Drawing) :
    arms x hw v k=some (s,d) ↔ ∃ i : Incidence x v,
      SatClusterStubs.slot x v i=k ∧ SatClusterStubs.side x hw v i=s ∧
        localDrawing x hw v (SatOwnerIncidences.edge x v i)=d := by
  unfold arms
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    exact ⟨i,(SatClusterStubs.atSlot_eq_some_iff x v k i).mp hi,
      congrArg Prod.fst he,congrArg Prod.snd he⟩
  · rintro ⟨i,hi,hs,hd⟩
    exact ⟨i,(SatClusterStubs.atSlot_eq_some_iff x v k i).mpr hi,Prod.ext hs hd⟩

theorem arms_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) :
    (arms x hw v).Valid := by
  constructor
  · intro k
    cases hk : SatClusterStubs.atSlot x v k with
    | none => simp [arms,hk,GridAssembly.Arm.Valid]
    | some i =>
      change GridAssembly.Arm.Valid ((SatClusterStubs.atSlot x v k).map _)
      rw [hk]
      exact ⟨localDrawing_valid x hw v _,localDrawing_docked x hw v hv i⟩
  · intro k l hkl
    cases hk : SatClusterStubs.atSlot x v k with
    | none => simp [arms,hk,GridAssembly.Arm.Apart]
    | some i =>
      cases hl : SatClusterStubs.atSlot x v l with
      | none => simp [arms,hl,GridAssembly.Arm.Apart]
      | some j =>
        have hij : i≠j := by
          intro he
          apply hkl
          exact ((SatClusterStubs.atSlot_eq_some_iff x v k i).mp hk).symm.trans
            ((congrArg (SatClusterStubs.slot x v) he).trans
              ((SatClusterStubs.atSlot_eq_some_iff x v l j).mp hl))
        have hs : SatClusterStubs.side x hw v i≠SatClusterStubs.side x hw v j :=
          fun h => hij (SatClusterStubs.side_injective x hw v h)
        change GridAssembly.Arm.Apart ((SatClusterStubs.atSlot x v k).map _)
          ((SatClusterStubs.atSlot x v l).map _)
        rw [hk,hl]
        exact ⟨hs,localDrawing_apart x hw v _ _ (fun h => hij (SatOwnerIncidences.edge_injective x v h))⟩

theorem points_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) (p : Point) :
    p∈(arms x hw v).points.image (SatNineClusterPlacement.frame x hw v).map ↔
      p∈SatNineClusterPlacement.points x hw v ∨
        ∃ e : Edge x,SatDockCorridors.owner x e=v ∧ p∈(SatCompleteTentacles.drawing x hw e).points := by
  constructor
  · rintro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rcases Finset.mem_union.mp hq with hq | hq
    · exact Or.inl (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
    · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hq
      cases he : SatClusterStubs.atSlot x v k with
      | none => simp [arms,he,GridAssembly.armPoints] at hk
      | some i =>
        have hm : q∈(localDrawing x hw v (SatOwnerIncidences.edge x v i)).points := by
          simpa only [arms,he,Option.map_some,GridAssembly.armPoints] using hk
        refine Or.inr ⟨SatOwnerIncidences.edge x v i,SatOwnerIncidences.owner_of_incidence x v hv i,?_⟩
        rw [← localDrawing_points x hw v _]
        exact Finset.mem_image.mpr ⟨q,hm,rfl⟩
  · rintro (hp | ⟨e,he,hp⟩)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨q,Finset.mem_union_left _ hq,rfl⟩
    · let i := SatOwnerIncidences.atOwnerVertex x v e he
      rw [← localDrawing_points x hw v e] at hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      apply Finset.mem_image.mpr
      refine ⟨q,Finset.mem_union_right _ ?_,rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨SatClusterStubs.slot x v i,Finset.mem_univ _,?_⟩
      rw [arms_slot]
      exact hq

theorem global_tip_color (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    color ((SatCompleteTentacles.drawing x hw e).tip 0)=0 := by
  rw [SatCompleteTentacles.drawing,TerminalCollarAttach.tip_color]
  simp [SatCompleteTentacles.anchor,SatNineClusterPlacement.anchor,LatticeSubdivision.scale,
    Int.add_emod,Int.mul_emod]

theorem local_tip_color (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) (e : Edge x) :
    color ((localDrawing x hw v e).tip 0)=0 := by
  have hc : SatNineClusterPlacement.color x v=0 := of_decide_eq_true hv
  have h := NineClusterPlacement.frame_color 64 (by decide)
    (SatBipartiteDrawing.point x hw v) (SatNineClusterPlacement.color x v)
    ((localDrawing x hw v e).tip 0)
  change color ((SatNineClusterPlacement.frame x hw v).map ((localDrawing x hw v e).tip 0))=_ at h
  rw [localDrawing_tip,global_tip_color,hc] at h
  simpa only [color,Fin.val_zero,Nat.cast_zero,Int.add_zero] using h.symm

theorem arm_port (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    GridAssembly.armPort (SatNineClusterPlacement.frame x hw v)
      (arms x hw v (SatClusterStubs.slot x v i))
        ((SatCompleteTentacles.drawing x hw (SatOwnerIncidences.edge x v i)).tip 0) := by
  rw [arms_slot]
  exact ⟨(localDrawing_tip x hw v _ 0).symm,local_tip_color x hw v hv _⟩

theorem ports_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.ownsTentacles x v =true) (p : Point) :
    (∃ k,GridAssembly.armPort (SatNineClusterPlacement.frame x hw v) (arms x hw v k) p) ↔
      ∃ e : Edge x,SatDockCorridors.owner x e=v ∧
        p=(SatCompleteTentacles.drawing x hw e).tip 0 := by
  constructor
  · rintro ⟨k,hk⟩
    cases he : SatClusterStubs.atSlot x v k with
    | none => simp [arms,he,GridAssembly.armPort] at hk
    | some i =>
      have hp : p=(SatNineClusterPlacement.frame x hw v).map
          ((localDrawing x hw v (SatOwnerIncidences.edge x v i)).tip 0) := by
        have hh : p=(SatNineClusterPlacement.frame x hw v).map
            ((localDrawing x hw v (SatOwnerIncidences.edge x v i)).tip 0) ∧
              color ((localDrawing x hw v (SatOwnerIncidences.edge x v i)).tip 0)=0 := by
          simpa only [arms,he,Option.map_some,GridAssembly.armPort] using hk
        exact hh.1
      exact ⟨SatOwnerIncidences.edge x v i,SatOwnerIncidences.owner_of_incidence x v hv i,
        hp.trans (localDrawing_tip x hw v _ 0)⟩
  · rintro ⟨e,he,rfl⟩
    let i := SatOwnerIncidences.atOwnerVertex x v e he
    exact ⟨SatClusterStubs.slot x v i,arm_port x hw v hv i⟩

theorem localDrawing_halfSize_bound (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (e : Edge x) :
    (localDrawing x hw v e).halfSize ≤ 12582912*(x.length+1)+17 := by
  rw [localDrawing,Drawing.transform_halfSize]
  have hc := SatCompleteTentacles.card_le x hw e
  rw [Drawing.card _ (SatCompleteTentacles.valid x hw e),
    Drawing.card _ (SatOwnerTentacles.valid x hw e)] at hc
  have hb := SatOwnerTentacles.halfSize_bound x hw e
  omega

theorem arms_halfSize_bound (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) :
    (∑ k : Fin 3,GridAssembly.armHalfSize (arms x hw v k)) ≤
      3*(12582912*(x.length+1)+17) := by
  have h (k : Fin 3) : GridAssembly.armHalfSize (arms x hw v k)≤
      12582912*(x.length+1)+17 := by
    cases hk : SatClusterStubs.atSlot x v k with
    | none => simp [arms,hk,GridAssembly.armHalfSize]
    | some i =>
      simpa only [arms,hk,Option.map_some,GridAssembly.armHalfSize] using
        localDrawing_halfSize_bound x hw v (SatOwnerIncidences.edge x v i)
  simpa using Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 3))) => h k)

end GridHardness.SatCompleteArms
