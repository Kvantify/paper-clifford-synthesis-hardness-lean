/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedIncidenceRecordCode
public import GridHardness.SatDirectedRouteLookupCode
public import GridHardness.SatBipartitePlacementCode

/-!
# SAT Directed Incidence Code

Incidence recovery and canonical port selection for actual SAT drawings.
The only frontend hypotheses are injective vertex labels and a complete
explicit list of the actual directed arcs; their enumeration order is free.
-/

public section

namespace GridHardness.SatDirectedIncidenceCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open SatCompleteDrawing DirectedPortSelectionCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1600000

variable (x : SatTy.denote) (hw : ∀ c∈x, c.length =3)

include hw in
theorem endpointDirection (a : Arc x) (b : Bool) :
    endpointDirectionCode.eval ((route x a).map encodePoint,b)=(direction x a b).val := by
  have hl : 2≤(route x a).length := by have := route_length_lower x a; omega
  rw [endpointDirectionCode_encoded _ b hl]
  have he : LatticeRouteDirections.endpointPoint (route x a) b hl=point x (endpointVertex x a b) := by
    apply Option.some.inj
    rw [← LatticeRouteDirections.endpointPoint_spec]
    cases b
    · exact (route_certificate x hw a).1
    · exact (route_certificate x hw a).2.1
  unfold LatticeRouteDirections.tangent
  rw [he, direction_spec x hw a b, LatticeRouteDirections.direction_step]

theorem mem_ports (v : Vertex x) (p : PortTy.denote) :
    p∈SatBipartitePlacementCode.records x v ↔
      ∃a:Arc x,∃b:Bool, endpointVertex x a b=v ∧ p=(b,(direction x a b).val) := by
  change p∈(SatBipartitePorts.incidencePorts x v).map encodePort ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨r,hr,hp⟩
    obtain ⟨i,hi⟩ := (SatBipartitePorts.mem_incidencePorts x v r).mp hr
    subst r
    exact ⟨i.val.1,i.val.2,i.property,hp.symm⟩
  · rintro ⟨a,b,hv,rfl⟩
    refine ⟨(b,direction x a b),?_,rfl⟩
    exact (SatBipartitePorts.mem_incidencePorts x v _).mpr ⟨⟨(a,b),hv⟩,rfl⟩

include hw in
theorem incidences (label : Vertex x → Nat) (hl : Function.Injective label)
    (arcs : List (Arc x)) (ha : ∀ a, a∈arcs) (v : Vertex x) (p : PortTy.denote) :
    p∈DirectedIncidenceRecordCode.code.eval
      (SatDirectedRouteLookupCode.records x label arcs,label v) ↔
      p∈SatBipartitePlacementCode.records x v := by
  rw [DirectedIncidenceRecordCode.mem_code,mem_ports]
  constructor
  · rintro ⟨r,hr,b,hv,hp⟩
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hr
    have hk : label v=label (endpointVertex x a b) := by
      cases b <;> exact hv
    refine ⟨a,b,(hl hk).symm,?_⟩
    rw [← endpointDirection x hw a b]
    exact hp
  · rintro ⟨a,b,hv,hp⟩
    refine ⟨SatDirectedRouteLookupCode.record x label a,List.mem_map_of_mem (ha a),b,?_,?_⟩
    · have hk := congrArg label hv.symm
      cases b <;> exact hk
    · rw [← endpointDirection x hw a b] at hp
      exact hp

/-- This is the very choice used by the migrated semantic drawing, even if
the executable frontend duplicates or reorders the arc records. -/
theorem selector (label : Vertex x → Nat) (hl : Function.Injective label)
    (arcs : List (Arc x)) (ha : ∀ a, a∈arcs) (v : Vertex x) :
    DirectedPortSelectionCode.code.eval (DirectedIncidenceRecordCode.code.eval
      (SatDirectedRouteLookupCode.records x label arcs,label v))=
      ((SatBipartitePorts.choose x hw v).incoming,(SatBipartitePorts.choose x hw v).direction.val) := by
  rw [DirectedPortSelectionCode.code_congr _ _ (incidences x hw label hl arcs ha v)]
  exact SatBipartitePlacementCode.selector x hw v

end GridHardness.SatDirectedIncidenceCode
