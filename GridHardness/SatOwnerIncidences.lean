/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDockCorridorSeparation
public import GridHardness.SatClusterStubs

/-!
# SAT Owner Incidences

Incidences at owning graph vertices correspond exactly to the actual
owner-oriented edge catalogue. This connects completed tentacles to the
three-slot arm assignment and identifies their recipient neighbors.
-/

@[expose] public section

namespace GridHardness.SatOwnerIncidences
open CliffordComplexity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatDockCorridors.Vertex
abbrev Edge := SatDockCorridors.Edge
abbrev Incidence := SatBipartiteDirections.Incidence

def edge (x : SatTy.denote) (v : Vertex x) (i : Incidence x v) : Edge x := i.val.1

/-- A catalogue edge has two distinct endpoints, so its incidence bit is
uniquely determined by the incident vertex. -/
theorem endpointBit_injective (x : SatTy.denote) (e : Edge x) :
    Function.Injective (SatBipartiteDirections.endpointVertex x e) := by
  intro b c he
  cases b <;> cases c
  · rfl
  · exact False.elim (SatBipartiteDrawing.endpoints_ne x e he)
  · exact False.elim (SatBipartiteDrawing.endpoints_ne x e he.symm)
  · rfl

/-- No edge occurs twice among the incidences at a fixed vertex. -/
theorem edge_injective (x : SatTy.denote) (v : Vertex x) : Function.Injective (edge x v) := by
  rintro ⟨⟨e,b⟩,hi⟩ ⟨⟨f,c⟩,hj⟩ hef
  change e=f at hef
  subst f
  have hbc := endpointBit_injective x e (hi.trans hj.symm)
  exact Subtype.ext (Prod.ext rfl hbc)

/-- At an owning vertex, every incident edge is oriented away from that
vertex by the actual asymmetric-corridor construction. -/
theorem owner_of_incidence (x : SatTy.denote) (v : Vertex x)
    (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    SatDockCorridors.owner x (edge x v i)=v := by
  have hi : v=SatBipartiteDrawing.source x (edge x v i) ∨
      v=SatBipartiteDrawing.target x (edge x v i) := by
    have h := i.property.symm
    cases hb : i.val.2
    · exact Or.inl (by simpa only [edge,hb,SatBipartiteDirections.endpointVertex,Bool.false_eq_true,ite_false] using h)
    · exact Or.inr (by simpa only [edge,hb,SatBipartiteDirections.endpointVertex,ite_true] using h)
  rcases (SatDockCorridors.incident_iff x (edge x v i) v).mpr hi with ho | hr
  · exact ho.symm
  · have h := (SatCollarCorridors.owners x (edge x v i)).2
    change SatNineClusterPlacement.ownsTentacles x (SatDockCorridors.recipient x (edge x v i))=false at h
    rw [← hr,hv] at h
    contradiction

theorem owner_of_color_zero (x : SatTy.denote) (v : Vertex x)
    (hv : SatNineClusterPlacement.color x v =0) (i : Incidence x v) :
    SatDockCorridors.owner x (edge x v i)=v :=
  owner_of_incidence x v (by simp [SatNineClusterPlacement.ownsTentacles,hv]) i

theorem bit_eq_reverse (x : SatTy.denote) (v : Vertex x)
    (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    i.val.2=SatDockCorridors.reverseEdge x (edge x v i) := by
  apply endpointBit_injective x (edge x v i)
  exact i.property.trans (owner_of_incidence x v hv i).symm

/-- Its selected owner side is exactly the side used by the existing
incidence-to-slot assignment. -/
theorem side_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x)
    (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    SatDockCorridors.side x hw (edge x v i) false=SatClusterStubs.side x hw v i := by
  unfold SatDockCorridors.side SatDockCorridors.direction SatClusterStubs.side
  simp only [Bool.false_eq_true,ite_false,bit_eq_reverse x v hv i]
  rfl

/-- The opposite endpoint stored by the incidence API is the actual
recipient of the completed owner tentacle. -/
theorem neighbor_eq_recipient (x : SatTy.denote) (v : Vertex x)
    (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    (SatClusterStubs.neighbor x v i).val=SatDockCorridors.recipient x (edge x v i) := by
  change SatBipartiteDirections.endpointVertex x i.val.1 (!i.val.2)=_
  rw [bit_eq_reverse x v hv i]
  rfl

/-- Every edge supplies its owning incidence without a choice. -/
def ownerIncidence (x : SatTy.denote) (e : Edge x) : Incidence x (SatDockCorridors.owner x e) :=
  ⟨(e,SatDockCorridors.reverseEdge x e),rfl⟩

@[simp] theorem edge_ownerIncidence (x : SatTy.denote) (e : Edge x) :
    edge x (SatDockCorridors.owner x e) (ownerIncidence x e)=e := rfl

/-- The same incidence viewed at any vertex proved equal to its owner. -/
def atOwnerVertex (x : SatTy.denote) (v : Vertex x) (e : Edge x)
    (he : SatDockCorridors.owner x e =v) : Incidence x v :=
  ⟨(e,SatDockCorridors.reverseEdge x e),he⟩

@[simp] theorem edge_atOwnerVertex (x : SatTy.denote) (v : Vertex x) (e : Edge x)
    (he : SatDockCorridors.owner x e =v) : edge x v (atOwnerVertex x v e he)=e := rfl

theorem atOwnerVertex_edge (x : SatTy.denote) (v : Vertex x)
    (hv : SatNineClusterPlacement.ownsTentacles x v =true) (i : Incidence x v) :
    atOwnerVertex x v (edge x v i) (owner_of_incidence x v hv i)=i :=
  edge_injective x v rfl

/-- In particular every edge appears at the owner's already reserved arm slot. -/
theorem owner_slot_present (x : SatTy.denote) (e : Edge x) :
    SatClusterStubs.atSlot x (SatDockCorridors.owner x e)
      (SatClusterStubs.slot x (SatDockCorridors.owner x e) (ownerIncidence x e))=
        some (ownerIncidence x e) := SatClusterStubs.atSlot_slot _ _ _

end GridHardness.SatOwnerIncidences
