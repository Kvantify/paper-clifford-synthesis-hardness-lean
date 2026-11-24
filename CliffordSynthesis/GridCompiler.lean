/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridProblems.Encoding
public import CliffordSynthesis.MatrixCompiler
public import CliffordSynthesis.BoundedGrid

/-!
# Grid Compiler

The input integers are differences of binary naturals. All loops run over
lists derived from the vertex list, never over the values of coordinates.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis.GridCompiler
open CliffordComplexity
open MatrixCompiler

abbrev AxisTy := Ty.pair (Ty.pair SignedTy .nat) (Ty.pair SignedTy .nat)
abbrev EnvTy := Ty.pair PointTy (Ty.pair .nat (Ty.list .nat))

def widthPad : Code InputTy RowTy :=
  .comp (.comp .fst (tailCode PointTy))
    (.comp (.listMap (.const RowTy [false, false])) .listJoin)

/-- One recorder plus six for every vertex after the first: `6 (M - 1) + 1`. -/
def copyPad : Code InputTy RowTy :=
  Code.cons (.const .bool false)
    (.comp (.comp .fst (tailCode PointTy))
      (.comp (.listMap (.const RowTy (List.replicate 6 false))) .listJoin))

/-- `((start, m), (point, threshold))`: translated unary bit, XOR the start bit. -/
def axisBit : Code AxisTy .bool :=
  let sPos : Code AxisTy .nat := .comp .fst (.comp .fst .fst)
  let sNeg : Code AxisTy .nat := .comp .fst (.comp .fst .snd)
  let m : Code AxisTy .nat := .comp .fst .snd
  let pPos : Code AxisTy .nat := .comp .snd (.comp .fst .fst)
  let pNeg : Code AxisTy .nat := .comp .snd (.comp .fst .snd)
  let j : Code AxisTy .nat := .comp .snd .snd
  .comp (.pair (Code.lt (Code.add (Code.add j pNeg) sPos) (Code.add (Code.add pPos sNeg) m))
    (Code.lt j m)) Code.boolNe

def axisBits : Code (.pair (.pair SignedTy .nat) (.pair SignedTy (Ty.list .nat))) RowTy :=
  .comp (.pair (.pair .fst (.comp .snd .fst)) (.comp .snd .snd))
    (.listMapEnv (.comp (.pair (.comp .fst .fst) (.pair (.comp .fst .snd) .snd)) axisBit))

def pointBits : Code (.pair EnvTy PointTy) RowTy :=
  let axis (projection : Code PointTy SignedTy) :=
    Code.comp
      (.pair (.pair (.comp (.comp .fst .fst) projection) (.comp .fst (.comp .snd .fst)))
        (.pair (.comp .snd projection) (.comp .fst (.comp .snd .snd)))) axisBits
  Code.append (axis .fst) (axis .snd)

def axisWithin : Code (.pair (.pair SignedTy .nat) SignedTy) .bool :=
  let sPos : Code (.pair (.pair SignedTy .nat) SignedTy) .nat := .comp .fst (.comp .fst .fst)
  let sNeg : Code (.pair (.pair SignedTy .nat) SignedTy) .nat := .comp .fst (.comp .fst .snd)
  let m : Code (.pair (.pair SignedTy .nat) SignedTy) .nat := .comp .fst .snd
  let pPos : Code (.pair (.pair SignedTy .nat) SignedTy) .nat := .comp .snd .fst
  let pNeg : Code (.pair (.pair SignedTy .nat) SignedTy) .nat := .comp .snd .snd
  Code.and
    (.comp (.pair (Code.add sPos pNeg) (Code.add (Code.add pPos sNeg) m)) .natLe)
    (.comp (.pair (Code.add pPos sNeg) (Code.add (Code.add sPos pNeg) m)) .natLe)

def pointWithin : Code (.pair (.pair PointTy .nat) PointTy) .bool :=
  let axis (projection : Code PointTy SignedTy) :=
    Code.comp (.pair (.pair (.comp (.comp .fst .fst) projection) (.comp .fst .snd))
      (.comp .snd projection)) axisWithin
  Code.and (axis .fst) (axis .snd)

def windowTest : Code InputTy .bool :=
  .comp (.pair (.pair start count) .fst) (.comp (.listMapEnv pointWithin) allCode)

def vertices : Code InputTy MatrixTy :=
  .comp (.pair (.pair start (.pair count (.comp widthPad Code.indices))) .fst)
    (.listMapEnv pointBits)

def repeated : Code InputTy MatrixTy :=
  .comp (.pair copyPad vertices)
    (.comp (.listMapEnv (.comp (.pair .snd .fst) (.listMapEnv .fst))) .listJoin)

def endBits : Code InputTy RowTy :=
  .comp (.pair vertices .snd) (.comp Code.listNth .listJoin)

def template : Code InputTy (.pair TemplateTy .nat) :=
  .pair (.pair endBits repeated) (Code.add (.comp repeated .listLen) count)

/-- A dense encoding of three-qubit fanout at threshold one. -/
def noOutput : OutputTy.denote :=
  ([[true, false, false], [true, true, false], [true, false, true]],
   ([[true, true, true], [false, true, false], [false, false, true]], 1))

def reduce : Code InputTy OutputTy :=
  .branch windowTest (.comp template MatrixCompiler.compile) (.const OutputTy noOutput)

end CliffordSynthesis.GridCompiler
