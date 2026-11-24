/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedPortSelectionCode
public import GridHardness.LatticeInterpolationCode

/-!
# Directed Bipartite Placement Code

Certified four-vertex bipartite replacement geometry. Given a directed
vertex anchor and its explicit incidence ports, the program selects a
canonical singleton side, outputs all four scaled gadget points, and supplies
the exact zero-or-three trimming radius at either directed side.
-/

@[expose] public section

namespace GridHardness.DirectedBipartitePlacementCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open DirectedPortSelection DirectedPortSelectionCode LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev PlacedTy := Ty.pair PointTy PortTy
abbrev InputTy := Ty.pair PointTy PortsTy

/-- A cardinal ray with a binary radius, defaulting to south on invalid
direction codes. Correctness for valid directions covers the actual compiler. -/
def rayCode : Code (.pair .nat .nat) PointTy :=
  let positive : Code (.pair .nat .nat) SignedTy := .pair .snd (.const .nat 0)
  let negative : Code (.pair .nat .nat) SignedTy := .pair (.const .nat 0) .snd
  let zero : Code (.pair .nat .nat) SignedTy := .const SignedTy (0,0)
  let test (d : Nat) : Code (.pair .nat .nat) .bool :=
    .comp (.pair .fst (.const .nat d)) .natEq
  .branch (test 0) (.pair positive zero)
    (.branch (test 1) (.pair zero positive)
      (.branch (test 2) (.pair negative zero) (.pair zero negative)))

theorem rayCode_eval (d : Fin 4) (n : Nat) :
    rayCode.eval (d.val,n)=encodePoint (DirectedLocalLayout.ray d n) := by
  fin_cases d <;> simp [rayCode, Code.eval, DirectedLocalLayout.ray, encodePoint, encodeInt]

def point : Code (.pair PlacedTy .nat) PointTy :=
  let c : Code (.pair PlacedTy .nat) PortTy := .comp .fst .snd
  let radius := .branch (.comp c .fst)
    (.comp (.pair (.const .nat 3) .snd) .natSub) .snd
  let offset := .comp (.pair (.comp c .snd) radius) rayCode
  let anchor := .comp (.comp .fst .fst) (scalePointCode 16)
  .pair (.comp (.pair (.comp anchor .fst) (.comp offset .fst)) addSigned)
    (.comp (.pair (.comp anchor .snd) (.comp offset .snd)) addSigned)

theorem point_eval (p : PointTy.denote) (c : Port) (i : Fin 4) :
    point.eval ((p,encodePort c),i.val) =
      encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 i) := by
  simp only [point, Code.eval, encodePort]
  rw [scalePointCode_eval, rayCode_eval, addSigned_eval, addSigned_eval]
  simp only [encodePoint, integer_encodeInt, DirectedScaledLayout.place,
    DirectedScaledLayout.anchor, DirectedLocalLayout.vertexPoint,
    LatticeSubdivision.scale]
  rfl

/-- The four replacement vertices, in their internal path order. -/
def points : Code PlacedTy CycleInputTy :=
  .comp (.pair .id (.const (.list .nat) [0,1,2,3])) (.listMapEnv point)

theorem points_eval (p : PointTy.denote) (c : Port) :
    points.eval (p,encodePort c) =
      [encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 0),
       encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 1),
       encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 2),
       encodePoint (DirectedScaledLayout.place (decoded p) c.2 c.1 3)] := by
  change [point.eval ((p,encodePort c),0),point.eval ((p,encodePort c),1),
    point.eval ((p,encodePort c),2),point.eval ((p,encodePort c),3)]=_
  simp only [List.cons.injEq]
  exact ⟨point_eval p c 0, point_eval p c 1, point_eval p c 2, point_eval p c 3, True.intro⟩

def radius : Code (.pair PortTy .bool) .nat :=
  .branch (.comp (.pair (.comp .fst .fst) .snd) GridFrameCode.xor)
    (.const .nat 0) (.const .nat 3)

theorem radius_eval (c : Port) (b : Bool) :
    radius.eval (encodePort c,b)=(if b=c.1 then 3 else 0) := by
  rcases c with ⟨a,d⟩
  cases a <;> cases b <;> rfl

def selected : Code InputTy PlacedTy := .pair .fst (.comp .snd DirectedPortSelectionCode.code)

theorem selected_eval (p : PointTy.denote) (rs : List Port) :
    selected.eval (p,rs.map encodePort)=(p,encodePort (choose rs)) := by
  change (p,DirectedPortSelectionCode.code.eval (rs.map encodePort))=_
  rw [DirectedPortSelectionCode.code_eval]

def code : Code InputTy CycleInputTy := .comp selected points

/-- Exact four-point output for the canonical choice, for arbitrary signed
binary input anchors and arbitrary incidence enumeration order. -/
theorem code_eval (p : PointTy.denote) (rs : List Port) :
    code.eval (p,rs.map encodePort) =
      [encodePoint (DirectedScaledLayout.place (decoded p) (choose rs).2 (choose rs).1 0),
       encodePoint (DirectedScaledLayout.place (decoded p) (choose rs).2 (choose rs).1 1),
       encodePoint (DirectedScaledLayout.place (decoded p) (choose rs).2 (choose rs).1 2),
       encodePoint (DirectedScaledLayout.place (decoded p) (choose rs).2 (choose rs).1 3)] := by
  change points.eval (selected.eval (p,rs.map encodePort))=_
  rw [selected_eval, points_eval]

/-- Both external trimming radii, outgoing then incoming. -/
def radii : Code PortsTy (.pair .nat .nat) :=
  .pair (.comp (.pair DirectedPortSelectionCode.code (.const .bool false)) radius)
    (.comp (.pair DirectedPortSelectionCode.code (.const .bool true)) radius)

theorem radii_eval (rs : List Port) :
    radii.eval (rs.map encodePort) =
      ((if false=(choose rs).1 then 3 else 0),(if true=(choose rs).1 then 3 else 0)) := by
  simp only [radii, Code.eval]
  rw [DirectedPortSelectionCode.code_eval, radius_eval, radius_eval]

end GridHardness.DirectedBipartitePlacementCode
