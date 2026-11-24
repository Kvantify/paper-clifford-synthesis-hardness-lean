/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteDrawing

/-!
# SAT Bipartite Directions

Distinct cardinal ports for all incidences of the simultaneous
bipartite drawing, including its two-point internal gadget routes. Exact
unordered edge uniqueness rules out coincident first steps even when a
neighboring point is already the other endpoint of an internal route.
-/

@[expose] public section

namespace GridHardness.SatBipartiteDirections
open CliffordComplexity CliffordSynthesis SatBipartiteDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- `false` selects the source and `true` the target. -/
def endpointVertex (x : SatTy.denote) (e : Edge x) (b : Bool) : Vertex x :=
  if b then target x e else source x e

noncomputable def direction (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) : Fin 4 :=
  LatticeRouteDirections.tangent (route x hw e) b (route_certificate x hw e).2.2.2.2.1

theorem endpointPoint_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    LatticeRouteDirections.endpointPoint (route x hw e) b
      (route_certificate x hw e).2.2.2.2.1=point x hw (endpointVertex x e b) := by
  have hs := LatticeRouteDirections.endpointPoint_spec (route x hw e) b
    (route_certificate x hw e).2.2.2.2.1
  have hc := route_certificate x hw e
  cases b
  · exact Option.some.inj (hs.symm.trans hc.1)
  · exact Option.some.inj (hs.symm.trans hc.2.1)

/-- The first step into either end of a route follows its chosen ray. -/
theorem direction_spec (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    LatticeRouteDirections.neighborPoint (route x hw e) b
      (route_certificate x hw e).2.2.2.2.1=
      LatticeRouteDirections.step (point x hw (endpointVertex x e b)) (direction x hw e b) := by
  have hc := route_certificate x hw e
  simpa only [endpointPoint_eq,direction] using
    LatticeRouteDirections.tangent_spec (route x hw e) b hc.2.2.2.2.1 hc.2.2.2.1

private theorem other_endpoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) (q : Point) (hq : Incident x hw e q)
    (hne : q ≠point x hw (endpointVertex x e b)) :
    q=point x hw (endpointVertex x e (!b)) := by
  cases b
  · exact hq.resolve_left hne
  · exact hq.resolve_right hne

/-- Distinct edges incident at one graph vertex use different cardinal
ports, even when one or both routes have only two points. -/
theorem direction_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (b c : Bool)
    (hv : endpointVertex x e b =endpointVertex x f c) :
    direction x hw e b≠direction x hw f c := by
  intro he
  have hce := route_certificate x hw e
  have hcf := route_certificate x hw f
  let q := LatticeRouteDirections.neighborPoint (route x hw e) b hce.2.2.2.2.1
  have hqf : q=LatticeRouteDirections.neighborPoint (route x hw f) c hcf.2.2.2.2.1 := by
    dsimp [q]
    rw [direction_spec,direction_spec,hv,he]
  have hqe : q∈route x hw e := LatticeRouteDirections.neighborPoint_mem _ _ _
  have hqm : q∈route x hw f := hqf.symm ▸ LatticeRouteDirections.neighborPoint_mem _ _ _
  obtain ⟨hie,hif⟩ := route_intersection x hw e f hef q hqe hqm
  have hne : q≠point x hw (endpointVertex x e b) := by
    have hu := LatticeRouteDirections.neighborPoint_step (route x hw e) b
      hce.2.2.2.2.1 hce.2.2.2.1
    rw [endpointPoint_eq] at hu
    change LatticeRouteDirections.UnitStep (point x hw (endpointVertex x e b)) q at hu
    intro heq
    rw [heq] at hu
    simp [LatticeRouteDirections.UnitStep,IntegerGrid.manhattan] at hu
  have hnf : q≠point x hw (endpointVertex x f c) := by simpa only [hv] using hne
  have ho : endpointVertex x e (!b)=endpointVertex x f (!c) :=
    point_injective x hw ((other_endpoint x hw e b q hie hne).symm.trans
      (other_endpoint x hw f c q hif hnf))
  apply hef
  apply SatBipartiteEdges.unordered_endpoints_injective x e f
  cases b <;> cases c
  · exact Or.inl ⟨hv,ho⟩
  · exact Or.inr ⟨hv,ho⟩
  · exact Or.inr ⟨ho,hv⟩
  · exact Or.inl ⟨ho,hv⟩

abbrev Incidence (x : SatTy.denote) (v : Vertex x) :=
  {i : Edge x × Bool // endpointVertex x i.1 i.2=v}

/-- All actual incidences occupy distinct cardinal ports at each vertex. -/
theorem incident_directions_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) :
    Function.Injective (fun i : Incidence x v => direction x hw i.val.1 i.val.2) := by
  rintro ⟨⟨e,b⟩,hi⟩ ⟨⟨f,c⟩,hj⟩ he
  dsimp at hi hj he
  apply Subtype.ext
  by_cases hef : e=f
  · subst f
    have hbc : b=c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (endpoints_ne x e (hi.trans hj.symm))
      · exact False.elim (endpoints_ne x e (hj.trans hi.symm))
      · rfl
    exact Prod.ext rfl hbc
  · exact False.elim (direction_ne x hw e f hef b c (hi.trans hj.symm) he)

end GridHardness.SatBipartiteDirections
