/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteTentacleSeparation
public import GridHardness.SatOwnerIncidences

/-!
# SAT Complete Ports

Canonical graph-neighbor ports for the completed geometric reduction.
The owning port is a tentacle tip; the receiving port is its cluster corner.
Unique edge indices make these choices consistent in both orientations.
-/

@[expose] public section

namespace GridHardness.SatCompletePorts
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxHeartbeats 1600000

abbrev Vertex := SatDockCorridors.Vertex
abbrev Edge := SatDockCorridors.Edge
abbrev graph := SatBipartiteDrawing.graph
abbrev owner := SatDockCorridors.owner
abbrev recipient := SatDockCorridors.recipient

/-- The owning orientation preserves each catalogue edge's unordered endpoints. -/
theorem edge_endpoints (x : SatTy.denote) (e : Edge x) :
    (owner x e=SatBipartiteDrawing.source x e ∧ recipient x e=SatBipartiteDrawing.target x e) ∨
      (owner x e=SatBipartiteDrawing.target x e ∧ recipient x e=SatBipartiteDrawing.source x e) := by
  unfold owner recipient SatDockCorridors.owner SatDockCorridors.recipient
    SatCollarCorridors.startVertex SatCollarCorridors.endVertex SatBipartiteDirections.endpointVertex
  cases h : SatCollarCorridors.reverseEdge x e <;> simp

theorem owner_recipient_injective (x : SatTy.denote) (e f : Edge x)
    (ho : owner x e =owner x f) (hr : recipient x e =recipient x f) : e=f := by
  apply SatBipartiteEdges.unordered_endpoints_injective x e f
  rcases edge_endpoints x e with ⟨heo,her⟩ | ⟨heo,her⟩ <;>
    rcases edge_endpoints x f with ⟨hfo,hfr⟩ | ⟨hfo,hfr⟩
  · exact Or.inl ⟨heo.symm.trans (ho.trans hfo),her.symm.trans (hr.trans hfr)⟩
  · exact Or.inr ⟨heo.symm.trans (ho.trans hfo),her.symm.trans (hr.trans hfr)⟩
  · exact Or.inr ⟨her.symm.trans (hr.trans hfr),heo.symm.trans (ho.trans hfo)⟩
  · exact Or.inl ⟨her.symm.trans (hr.trans hfr),heo.symm.trans (ho.trans hfo)⟩

theorem adjacency_iff (x : SatTy.denote) (v w : Vertex x) :
    (graph x).Adj v w ↔ ∃ e : Edge x,
      (owner x e=v ∧ recipient x e=w) ∨ (owner x e=w ∧ recipient x e=v) := by
  constructor
  · intro h
    obtain ⟨e,he⟩ := (SatBipartiteEdges.adjacency_iff x v w).mp h
    refine ⟨e,?_⟩
    rcases edge_endpoints x e with ⟨ho,hr⟩ | ⟨ho,hr⟩ <;>
      rcases he with ⟨hv,hw⟩ | ⟨hw,hv⟩
    · exact Or.inl ⟨ho.trans hv,hr.trans hw⟩
    · exact Or.inr ⟨ho.trans hw,hr.trans hv⟩
    · exact Or.inr ⟨ho.trans hw,hr.trans hv⟩
    · exact Or.inl ⟨ho.trans hv,hr.trans hw⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact SatCollarCorridors.endpoints_adj x e
    · exact (SatCollarCorridors.endpoints_adj x e).symm

/-- Total port function. Adjacent vertices use the uniquely indexed edge;
unrelated pairs receive an unused default point. -/
noncomputable def port (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w : Vertex x) : Point := by
  classical
  exact if h : ∃ e : Edge x,owner x e=v ∧ recipient x e=w then
    (SatCompleteTentacles.drawing x hw (Classical.choose h)).tip 0
  else if h : ∃ e : Edge x,owner x e=w ∧ recipient x e=v then
    SatNineClusterPlacement.corner x hw v (SatCompleteTentacles.side x hw (Classical.choose h))
  else (0,0)

theorem port_owner (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    port x hw (owner x e) (recipient x e)=(SatCompleteTentacles.drawing x hw e).tip 0 := by
  classical
  have h : ∃ f : Edge x,owner x f=owner x e ∧ recipient x f=recipient x e := ⟨e,rfl,rfl⟩
  have he : Classical.choose h=e := owner_recipient_injective x _ e
    (Classical.choose_spec h).1 (Classical.choose_spec h).2
  simp only [port,dite_eq_left h,he]

theorem port_recipient (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    port x hw (recipient x e) (owner x e)=
      SatNineClusterPlacement.corner x hw (recipient x e) (SatCompleteTentacles.side x hw e) := by
  classical
  have hno : ¬∃ f : Edge x,owner x f=recipient x e ∧ recipient x f=owner x e := by
    rintro ⟨f,hf,_⟩
    exact SatDockCorridors.owner_recipient_ne x f e hf
  have h : ∃ f : Edge x,owner x f=owner x e ∧ recipient x f=recipient x e := ⟨e,rfl,rfl⟩
  have he : Classical.choose h=e := owner_recipient_injective x _ e
    (Classical.choose_spec h).1 (Classical.choose_spec h).2
  simp only [port,dite_eq_right hno,dite_eq_left h,he]

/-- Each adjacent pair has a catalogue witness and both canonical port
coordinates, simultaneously, in whichever owning orientation applies. -/
theorem adjacent_spec (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w : Vertex x)
    (hvw : (graph x).Adj v w) :
    ∃ e : Edge x,
      (owner x e=v ∧ recipient x e=w ∧
        port x hw v w=(SatCompleteTentacles.drawing x hw e).tip 0 ∧
        port x hw w v=SatNineClusterPlacement.corner x hw w (SatCompleteTentacles.side x hw e)) ∨
      (owner x e=w ∧ recipient x e=v ∧
        port x hw w v=(SatCompleteTentacles.drawing x hw e).tip 0 ∧
        port x hw v w=SatNineClusterPlacement.corner x hw v (SatCompleteTentacles.side x hw e)) := by
  obtain ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacency_iff x v w).mp hvw
  · exact ⟨e,Or.inl ⟨rfl,rfl,port_owner x hw e,port_recipient x hw e⟩⟩
  · exact ⟨e,Or.inr ⟨rfl,rfl,port_owner x hw e,port_recipient x hw e⟩⟩

theorem corner_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    Function.Injective (SatNineClusterPlacement.corner x hw v) := by
  intro s t he
  have h : NineClusterAttachment.corner s=NineClusterAttachment.corner t :=
    (SatNineClusterPlacement.frame x hw v).injective he
  exact (by decide : Function.Injective NineClusterAttachment.corner) h

/-- Different graph neighbors use different points of their common region. -/
theorem distinctPorts (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w z : Vertex x)
    (hvw : (graph x).Adj v w) (hvz : (graph x).Adj v z) (hwz : w ≠z) :
    port x hw v w≠port x hw v z := by
  obtain ⟨e,he⟩ := adjacent_spec x hw v w hvw
  obtain ⟨f,hf⟩ := adjacent_spec x hw v z hvz
  intro hp
  rcases he with ⟨heo,her,hep,heq⟩ | ⟨heo,her,hep,heq⟩ <;>
    rcases hf with ⟨hfo,hfr,hfp,hfq⟩ | ⟨hfo,hfr,hfp,hfq⟩
  · have hef : e≠f := fun h => hwz (her.symm.trans ((congrArg (recipient x) h).trans hfr))
    rw [hep,hfp] at hp
    have hpe := (SatCompleteTentacles.drawing x hw e).tip_mem (SatCompleteTentacles.valid x hw e) 0
    have hpf := (SatCompleteTentacles.drawing x hw f).tip_mem (SatCompleteTentacles.valid x hw f) 0
    exact Finset.disjoint_left.mp (SatCompleteTentacles.pairwise_apart x hw e f hef).1
      hpe (hp.symm ▸ hpf)
  · exact SatDockCorridors.owner_recipient_ne x e f (heo.trans hfr.symm)
  · exact SatDockCorridors.owner_recipient_ne x f e (hfo.trans her.symm)
  · have hef : e≠f := fun h => hwz (heo.symm.trans ((congrArg (owner x) h).trans hfo))
    rw [heq,hfq] at hp
    have hs := corner_injective x hw v hp
    exact SatDockCorridors.recipient_sides_ne x hw e f hef (her.trans hfr.symm) hs

end GridHardness.SatCompletePorts
