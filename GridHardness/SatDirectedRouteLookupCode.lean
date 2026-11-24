/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedRouteLookupCode
public import GridHardness.SatCompleteDrawing

/-!
# SAT Directed Route Lookup Code

Exact lookup of the currently selected SAT routes from explicit records.
Actual arcs are ordered pairs of vertices, so injective vertex labels make
their endpoint keys functional without any width-three or geometric premise.
Constructing these route records, including the catalogue-index selection,
is deliberately outside this lookup program's resource claim.
-/

@[expose] public section

namespace GridHardness.SatDirectedRouteLookupCode
open CliffordComplexity GridProblems GridProblems.GridCode SatCompleteDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

variable (x : SatTy.denote) (label : Vertex x → Nat)

def key (a : Arc x) : DirectedRouteLookupCode.KeyTy.denote :=
  (label (source x a),label (target x a))

noncomputable def record (a : Arc x) : DirectedRouteLookupCode.RecordTy.denote :=
  (key x label a,(route x a).map encodePoint)

noncomputable def records (arcs : List (Arc x)) : DirectedRouteLookupCode.RecordsTy.denote :=
  arcs.map (record x label)

theorem key_injective (hl : Function.Injective label) : Function.Injective (key x label) := by
  intro a b he
  apply Subtype.ext
  exact Prod.ext (hl (congrArg Prod.fst he)) (hl (congrArg Prod.snd he))

/-- Repetition and enumeration order are harmless because actual arcs with
equal ordered endpoints are the same subtype value. -/
theorem functional (arcs : List (Arc x)) (hl : Function.Injective label) :
    DirectedRouteLookupCode.Functional (records x label arcs) := by
  intro r hr s hs he
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hs
  have hab := key_injective x label hl he
  rw [hab]

/-- The program returns the semantic route of the requested arc.
`SatDrawingSelectionCode` supplies these records directly from SAT syntax. -/
theorem route_eval (arcs : List (Arc x)) (hl : Function.Injective label)
    (a : Arc x) (ha : a ∈arcs) :
    DirectedRouteLookupCode.code.eval (records x label arcs,key x label a)=
      (route x a).map encodePoint := by
  exact DirectedRouteLookupCode.code_eq_of_mem _ _ _
    (List.mem_map_of_mem ha) (functional x label arcs hl)

theorem order_independent (arcs bs : List (Arc x)) (hl : Function.Injective label)
    (he : ∀ a, a∈arcs ↔ a ∈bs) (q : DirectedRouteLookupCode.KeyTy.denote) :
    DirectedRouteLookupCode.code.eval (records x label arcs,q)=
      DirectedRouteLookupCode.code.eval (records x label bs,q) := by
  apply DirectedRouteLookupCode.code_order_independent _ _ _ (functional x label arcs hl)
  intro r
  simp only [records,List.mem_map,he]

end GridHardness.SatDirectedRouteLookupCode
