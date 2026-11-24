/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteRuns

/-!
# Lattice Route Run Scan

A bounded-position description of maximal straight runs. This agrees
with recursive run compression and can be compiled without a general fold.
-/

@[expose] public section

namespace GridHardness.LatticeRouteRunsCode
set_option autoImplicit false

abbrev NatRun := Nat×Nat

def encodeRun (r : LatticeRouteRuns.Run) : NatRun := (r.1.val,r.2)

def prependNat (d : Nat) : List NatRun → List NatRun
  | [] => [(d,1)]
  | (e,n)::rs => if d=e then (e,n+1)::rs else (d,1)::(e,n)::rs

def compressNat : List Nat → List NatRun
  | [] => []
  | d::ds => prependNat d (compressNat ds)

/-- Emit a record only at the beginning of a maximal constant block. -/
def scan (prev : Option Nat) : List Nat → List NatRun
  | [] => []
  | d::ds => if prev=some d then scan (some d) ds
    else (d,(ds.takeWhile (fun e => decide (d=e))).length+1)::scan (some d) ds

theorem compressNat_cons (d : Nat) (ds : List Nat) :
    compressNat (d::ds)=
      (d,(ds.takeWhile (fun e => decide (d=e))).length+1)::scan (some d) ds := by
  induction ds generalizing d with
  | nil => rfl
  | cons e ds ih =>
    rw [compressNat,ih e]
    by_cases he : d=e
    · subst e
      simp [prependNat,scan,List.takeWhile_cons,Nat.add_assoc]
    · simp [prependNat,scan,List.takeWhile_cons,he]

theorem scan_none (ds : List Nat) : scan none ds=compressNat ds := by
  cases ds with
  | nil => rfl
  | cons d ds => simp [scan,compressNat_cons]

theorem prependNat_encode (d : Fin 4) (rs : List LatticeRouteRuns.Run) :
    prependNat d.val (rs.map encodeRun)=(LatticeRouteRuns.prepend d rs).map encodeRun := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    rcases r with ⟨e,n⟩
    by_cases he : d=e
    · subst e; simp [prependNat,LatticeRouteRuns.prepend,encodeRun]
    · have hv : d.val≠e.val := fun h => he (Fin.ext h)
      simp [prependNat,LatticeRouteRuns.prepend,encodeRun,he,hv]

theorem compressNat_encode (ds : List (Fin 4)) :
    compressNat (ds.map Fin.val)=(LatticeRouteRuns.compressDirections ds).map encodeRun := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.map_cons,compressNat,ih,prependNat_encode,LatticeRouteRuns.compressDirections]

/-- Previous value at a list position, with an external initial predecessor. -/
def previous (prev : Option Nat) (xs : List Nat) (i : Nat) : Option Nat :=
  if i=0 then prev else xs[i-1]?

def enumScan (prev : Option Nat) (xs : List Nat) : List NatRun :=
  xs.zipIdx.flatMap (fun q =>
    if previous prev xs q.2=some q.1 then []
    else [(q.1,((xs.drop q.2).takeWhile (fun e => decide (q.1=e))).length)])

theorem previous_cons (prev : Option Nat) (a : Nat) (xs : List Nat) (i : Nat) :
    previous prev (a::xs) (i+1)=previous (some a) xs i := by
  cases i <;> simp [previous]

theorem enumScan_cons (prev : Option Nat) (a : Nat) (xs : List Nat) :
    enumScan prev (a::xs)=
      (if prev=some a then []
      else [(a,(xs.takeWhile (fun e => decide (a=e))).length+1)]) ++ enumScan (some a) xs := by
  unfold enumScan
  rw [List.zipIdx_cons']
  simp only [List.flatMap_cons,List.flatMap_map,previous,ite_true,List.drop_zero,
    List.takeWhile_cons,decide_true,ite_true,List.length_cons]
  congr 1
  apply List.flatMap_congr
  intro q _
  rcases q with ⟨d,i⟩
  simp only [Prod.map,id_eq,Function.comp_def,List.drop_succ_cons]
  have he := previous_cons prev a xs i
  simp only [previous] at he
  rw [he]

theorem enumScan_eq_scan (prev : Option Nat) (xs : List Nat) : enumScan prev xs=scan prev xs := by
  induction xs generalizing prev with
  | nil => rfl
  | cons a xs ih =>
    rw [enumScan_cons,ih]
    by_cases he : prev=some a <;> simp [scan,he]

/-- The position scan computes exactly the established maximal-run compression. -/
theorem enumScan_encode (ds : List (Fin 4)) :
    enumScan none (ds.map Fin.val)=(LatticeRouteRuns.compressDirections ds).map encodeRun := by
  rw [enumScan_eq_scan,scan_none,compressNat_encode]

end GridHardness.LatticeRouteRunsCode
