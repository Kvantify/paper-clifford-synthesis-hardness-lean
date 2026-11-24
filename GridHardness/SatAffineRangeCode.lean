/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCode

/-!
# SAT Affine Range Code

Affine loop bounds are generated from the explicit clause list, so
enumerating them is polynomial even though natural numbers use binary size.
-/

@[expose] public section

namespace GridHardness.SatAffineRangeCode
open CliffordComplexity
set_option autoImplicit false

def padding (a b : Nat) : Code SatTy (.list .nat) :=
  Code.append (.comp (.listMap (.const (.list .nat) (List.replicate a 0))) .listJoin)
    (.const (.list .nat) (List.replicate b 0))

theorem padding_length (a b : Nat) (x : SatTy.denote) :
    ((padding a b).eval x).length=a*x.length+b := by
  change ((x.map (fun _ => List.replicate a 0)).flatten ++ List.replicate b 0).length=_
  simp [List.length_flatten,Nat.mul_comm]

def code (a b : Nat) : Code SatTy (.list .nat) := .comp (padding a b) Code.indices

theorem code_eval (a b : Nat) (x : SatTy.denote) :
    (code a b).eval x=List.range (a*x.length+b) := by
  rw [code,Code.eval,indices_eval,padding_length]

end GridHardness.SatAffineRangeCode
