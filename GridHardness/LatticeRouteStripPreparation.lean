/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRunsCode
public import GridHardness.SignedRunCode
public import GridHardness.SignedTentacleCardinalFrames

/-!
# Lattice Route Strip Preparation

Prepare an encoded point route for the signed-strip compiler. The route
itself supplies all unary padding; no run length is used as a loop bound.
-/

@[expose] public section

namespace GridHardness.LatticeRouteStripCode
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open GridProblems GridProblems.GridCode GridPointCode LatticeRouteRunsCode LatticeRouteCodeLists SignedRunCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair StateTy CycleInputTy
abbrev PreparedTy := Ty.pair StateTy (.pair .nat (.pair RunsTy PaddingTy))

def compressed : Code InputTy RunsTy := .comp .snd routeCode

def firstLength : Code InputTy .nat :=
  .comp (.pair compressed (.const .nat 0)) (lookupNat RunTy .snd)

def remaining : Code InputTy RunsTy :=
  .comp (.pair compressed (.const .nat 1)) (dropCode RunTy)

def reservoir : Code InputTy PaddingTy := .comp .snd (.listMap (.const .bool false))

def prepare : Code InputTy PreparedTy :=
  .pair .fst (.pair firstLength (.pair remaining reservoir))

theorem reservoir_eval (s : StateTy.denote) (xs : CycleInputTy.denote) :
    reservoir.eval (s,xs)=List.replicate xs.length false := by
  exact List.map_const' (l:=xs) (b:=false)

theorem firstLength_eval (s : StateTy.denote) (xs : CycleInputTy.denote)
    (d : Fin 4) (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hc : LatticeRouteRuns.compress (xs.map decoded) =(d,n)::rs) :
    firstLength.eval (s,xs)=n := by
  change (lookupNat RunTy Code.snd).eval (routeCode.eval xs,0)=_
  rw [routeCode_eval,hc,List.map_cons]
  rw [lookupNat_eval RunTy Code.snd _ 0 (by simp)]
  rfl

theorem remaining_eval (s : StateTy.denote) (xs : CycleInputTy.denote)
    (d : Fin 4) (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hc : LatticeRouteRuns.compress (xs.map decoded) =(d,n)::rs) :
    remaining.eval (s,xs)=rs.map encodeRun := by
  change (dropCode RunTy).eval (routeCode.eval xs,1)=_
  rw [dropCode_eval,routeCode_eval,hc,List.map_cons]
  rfl

theorem prepare_eval (s : RunState) (xs : CycleInputTy.denote)
    (n : Nat) (rs : List LatticeRouteRuns.Run)
    (hc : LatticeRouteRuns.compress (xs.map decoded) =(s.frame.axisDirection,n)::rs) :
    prepare.eval (encodeState s,xs)=(encodeState s,n,rs.map encodeRun,List.replicate xs.length false) := by
  change (encodeState s,firstLength.eval (encodeState s,xs),
    remaining.eval (encodeState s,xs),reservoir.eval (encodeState s,xs))=_
  rw [firstLength_eval _ _ _ _ _ hc,remaining_eval _ _ _ _ _ hc,reservoir_eval]

theorem reservoir_bounds (xs : CycleInputTy.denote) (d : Fin 4) (n : Nat)
    (rs : List LatticeRouteRuns.Run)
    (hc : LatticeRouteRuns.compress (xs.map decoded) =(d,n)::rs) :
    n≤xs.length ∧ ∀ r∈rs,r.2≤xs.length := by
  have he : routeCode.eval xs=encodeRun (d,n)::rs.map encodeRun := by
    rw [routeCode_eval,hc,List.map_cons]
  constructor
  · exact routeCode_run_le_length xs (encodeRun (d,n)) (by rw [he]; exact List.mem_cons_self)
  · intro r hr
    exact routeCode_run_le_length xs (encodeRun r)
      (by rw [he]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr))

/-- Simple unit routes automatically supply the required right-angle turns. -/
theorem compressed_perpendicular (xs : CycleInputTy.denote) (d : Fin 4) (n : Nat)
    (rs : List LatticeRouteRuns.Run)
    (hc : LatticeRouteRuns.compress (xs.map decoded) =(d,n)::rs)
    (hn : (xs.map decoded).Nodup)
    (hu : (xs.map decoded).IsChain LatticeSubdivision.UnitStep) :
    (d::rs.map Prod.fst).IsChain (fun d e => d.val%2≠e.val%2) := by
  have h := LatticeRouteRuns.runs_perpendicular (xs.map decoded) hn hu
  rw [hc,List.map_cons] at h
  exact h

end GridHardness.LatticeRouteStripCode
