/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleEndpointLocality
public import GridHardness.SignedTentacleGraft
public import GridHardness.NineClusterAttachment

/-!
# Signed Tentacle Run Docking

Syntactic docking certificates for compiled strip chains. Every
noninitial strip is controlled through the generated segment list; this
stronger tail statement distinguishes true docking from point-set locality.
-/

public section

namespace GridHardness.NineClusterAttachment
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem clear_union (S T : Finset Point) : Clear (S∪T) ↔ Clear S ∧ Clear T := by
  simp only [Clear,Finset.disjoint_union_right,Finset.mem_union]
  constructor
  · rintro ⟨⟨hS,hT⟩,h⟩
    exact ⟨⟨hS,fun c hc t ht => h c hc t (Or.inl ht)⟩,
      ⟨hT,fun c hc t ht => h c hc t (Or.inr ht)⟩⟩
  · rintro ⟨⟨hS,hs⟩,⟨hT,ht⟩⟩
    refine ⟨⟨hS,hT⟩,?_⟩
    intro c hc t hmem
    rcases hmem with hmem | hmem
    · exact hs c hc t hmem
    · exact ht c hc t hmem

/-- The recursive docking predicate is exactly an initial-frame condition
and clearance of the union of all strips added after the initial strip. -/
theorem docked_iff_base_tail (b : Bool) (side : Fin 4) (d : Drawing) :
    Docked b side d ↔ d.baseFrame=dock b side ∧ Clear d.tailPoints := by
  induction d with
  | base f n => simp [Docked,Drawing.baseFrame,Drawing.tailPoints,Clear]
  | attach d f n ih =>
    simp only [Docked,Drawing.baseFrame,Drawing.tailPoints,clear_union,ih]
    tauto

/-- A quantitative gap from the local cluster center implies the exact
finite disjointness and nonadjacency predicate used by docking. -/
theorem clear_of_center_distance (S : Finset Point)
    (h : ∀ p ∈ S, 4 ≤IntegerGrid.manhattan (1, 1) p) : Clear S := by
  have hr (p : Point) (hp : p∈points) : IntegerGrid.manhattan (1,1) p≤2 := by
    have hb := (mem_points_iff p).mp hp
    dsimp [IntegerGrid.manhattan]
    omega
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hps
    have hnear := hr p hp
    have hfar := h p hps
    omega
  · intro c hc p hp ha
    have hnear := hr c hc
    have hfar := h p hp
    have ht := IntegerGrid.manhattan_triangle (1,1) c p
    change IntegerGrid.manhattan c p=1 at ha
    omega

end GridHardness.NineClusterAttachment

namespace GridHardness.SignedTentacle.RunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Executing requests adds precisely their generated strips to the
existing tail, without counting the original base strip as a tail strip. -/
theorem execute_tail_mem (d : Drawing) (s : RunState) (length : Nat)
    (rs : List Request) (p : Point) :
    p∈(execute d s length rs).tailPoints ↔
      p∈d.tailPoints ∨ ∃ a∈(runs s length rs).tail,p∈segmentStrip a := by
  induction rs generalizing d s length with
  | nil => simp [execute,runs]
  | cons request rs ih =>
    rcases request with ⟨down,n⟩
    rw [execute,ih]
    change (p∈d.tailPoints∪segmentStrip (s.advance length down,n) ∨
      ∃ a∈(runs (s.advance length down) n rs).tail,p∈segmentStrip a) ↔
      p∈d.tailPoints ∨ ∃ a∈runs (s.advance length down) n rs,p∈segmentStrip a
    conv_rhs => rw [runs_self_tail]
    simp only [Finset.mem_union,List.mem_cons,exists_eq_or_imp]
    tauto

theorem compile_tail_mem (s : RunState) (length : Nat) (rs : List Request) (p : Point) :
    p∈(compile s length rs).tailPoints ↔
      ∃ a∈(runs s length rs).tail,p∈segmentStrip a := by
  rw [compile,execute_tail_mem]
  simp [Drawing.tailPoints]

theorem execute_baseFrame (d : Drawing) (s : RunState) (length : Nat) (rs : List Request) :
    (execute d s length rs).baseFrame=d.baseFrame := by
  induction rs generalizing d s length with
  | nil => rfl
  | cons r rs ih => cases r; exact ih _ _ _

theorem compile_baseFrame (s : RunState) (length : Nat) (rs : List Request) :
    (compile s length rs).baseFrame=s.frame := execute_baseFrame _ _ _ _

end GridHardness.SignedTentacle.RunChain

namespace GridHardness.SignedTentacle.CardinalRunChain
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every point on a noninitial strip stays far from the ideal start,
even if it also belongs to a neighboring strip. The estimate therefore
controls the syntactic tail rather than merely the complement of the base. -/
theorem compile_tail_distance (s : RunState) (length : Nat) (rs : List Run)
    (scale lower : Nat)
    (hc : (s.frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2≠e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns (s.point 0) ((s.frame.axisDirection,length)::rs)))
    (hn : ∀ r ∈(s.frame.axisDirection,length)::rs, lower ≤ r.2)
    (p : Point) (hp : p ∈ (RunChain.compile s length (requests s length rs)).tailPoints) :
    min scale lower≤IntegerGrid.manhattan (s.point 0) p+2 := by
  obtain ⟨a,ha,hpa⟩ := (RunChain.compile_tail_mem s length (requests s length rs) p).mp hp
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem ha
  have hi' : i+1<(RunChain.runs s length (requests s length rs)).length := by
    simp only [List.length_tail] at hi
    omega
  rw [List.getElem_tail] at hpa
  obtain ⟨k,hk0,hka,hkp⟩ :=
    ((RunChain.runs s length (requests s length rs))[i+1]'hi').1.strip_distance
      ((RunChain.runs s length (requests s length rs))[i+1]'hi').2 p hpa
  have hd := requests_start_distance s length rs scale lower hc hs hn (i+1) hi'
    (by omega) k hk0 hka
  have ht := IntegerGrid.manhattan_triangle (s.point 0) p
    (((RunChain.runs s length (requests s length rs))[i+1]'hi').1.point k)
  omega

end GridHardness.SignedTentacle.CardinalRunChain
