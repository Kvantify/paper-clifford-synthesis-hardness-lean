/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FreeLayers

/-!
# Two Qubit Algebra

Finite binary symplectic semantics of an arbitrary two-qubit Clifford.
Coordinates are ordered X₀,Z₀,X₁,Z₁.
-/

@[expose] public section

namespace CliffordSynthesis.TwoQubit

abbrev Bits := Bool × Bool × Bool × Bool
abbrev Matrix := BitVec 16

def row (p : Matrix) (i : Nat) : BitVec 4 := p.extractLsb' (4 * i) 4

def dot (p : BitVec 4) (v : Bits) : Bool :=
  (p.getLsbD 0 && v.1) ^^ (p.getLsbD 1 && v.2.1) ^^
  (p.getLsbD 2 && v.2.2.1) ^^ (p.getLsbD 3 && v.2.2.2)

def action (p : Matrix) (v : Bits) : Bits :=
  (dot (row p 0) v, dot (row p 1) v, dot (row p 2) v, dot (row p 3) v)

def gram (p q : BitVec 4) : Bool :=
  (p.getLsbD 0 && q.getLsbD 1) ^^ (p.getLsbD 1 && q.getLsbD 0) ^^
  (p.getLsbD 2 && q.getLsbD 3) ^^ (p.getLsbD 3 && q.getLsbD 2)

/-- All six off-diagonal entries of M J Mᵀ = J. The diagonal entries vanish
identically in characteristic two. -/
def valid (p : Matrix) : Bool :=
  gram (row p 0) (row p 1) && gram (row p 2) (row p 3) &&
  !(gram (row p 0) (row p 2)) && !(gram (row p 0) (row p 3)) &&
  !(gram (row p 1) (row p 2)) && !(gram (row p 1) (row p 3))

structure Normal where
  before₀ : Fin 6
  before₁ : Fin 6
  cnot : Bool
  after₀ : Fin 6
  after₁ : Fin 6
  swap : Bool
  deriving DecidableEq

def localAction (f g : Fin 6) (v : Bits) : Bits :=
  let a := FreeLayers.act f (v.1, v.2.1)
  let b := FreeLayers.act g (v.2.2.1, v.2.2.2)
  (a.1, a.2, b.1, b.2)

def cnotAction (v : Bits) : Bits := (v.1, v.2.1 ^^ v.2.2.2, v.2.2.1 ^^ v.1, v.2.2.2)
def swapAction (v : Bits) : Bits := (v.2.2.1, v.2.2.2, v.1, v.2.1)

def normalAction (f : Normal) (v : Bits) : Bits :=
  let u := localAction f.before₀ f.before₁ v
  let u := if f.cnot then cnotAction u else u
  let u := localAction f.after₀ f.after₁ u
  if f.swap then swapAction u else u

end CliffordSynthesis.TwoQubit
