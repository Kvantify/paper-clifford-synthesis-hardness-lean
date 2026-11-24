/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCodeLists

/-!
# Bounded Range Code

Enumerating a binary length using explicit list fuel. The bound is part
of correctness, not a hidden unbounded loop in the certificate language.
-/

@[expose] public section

namespace GridHardness.BoundedRangeCode
open CliffordComplexity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def code (τ : Ty) : Code (.pair (.list τ) .nat) (.list .nat) :=
  .comp (.pair .snd (.comp .fst Code.indices))
    (Code.filterEnv (Code.lt .snd .fst))

theorem filter_range (n m : Nat) :
    (List.range n).filter (fun k => decide (k<m))=List.range (min n m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.filter_append,ih]
    by_cases h : n<m
    · have h₀ : min n m=n := by omega
      have h₁ : min (n+1) m=n+1 := by omega
      simp [h,h₀,h₁,List.range_succ]
    · have h₀ : min n m=m := by omega
      have h₁ : min (n+1) m=m := by omega
      simp [h,h₀,h₁]

theorem code_eval (τ : Ty) (xs : List τ.denote) (n : Nat) :
    (code τ).eval (xs,n)=List.range (min xs.length n) := by
  change (Code.filterEnv (Code.lt .snd .fst)).eval
    (n,(Code.indices (τ:=τ)).eval xs)=_
  rw [indices_eval,filterEnv_eval]
  change (List.range xs.length).filter (fun a => Code.natLt.eval (a,n))=_
  calc
    _=(List.range xs.length).filter (fun a => decide (a<n)) := by
      apply List.filter_congr
      intro a _
      exact natLt_eval a n
    _= _ := filter_range xs.length n

theorem code_eval_of_le (τ : Ty) (xs : List τ.denote) (n : Nat) (hn : n ≤xs.length) :
    (code τ).eval (xs,n)=List.range n := by
  rw [code_eval,Nat.min_eq_right hn]

end GridHardness.BoundedRangeCode
