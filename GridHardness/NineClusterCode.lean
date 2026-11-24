/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridDrawingTemplateCode
public import GridHardness.NineClusterPlacement

/-!
# Nine Cluster Code

Certified placement of a nine-cluster from an arbitrary signed anchor,
binary dilation factor, and checkerboard phase. Scaling changes only binary
coordinates: the output rectangle always has two fixed three-element paddings.
The phase gives the actual corner color when the dilation is even.
-/

@[expose] public section

namespace GridHardness.NineClusterCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Multiplication by a binary natural, with canonical signed output. -/
def scaleSigned : Code (.pair .nat SignedTy) SignedTy :=
  .comp (.pair (Code.mul .fst (.comp .snd .fst))
    (Code.mul .fst (.comp .snd .snd))) normalize

theorem scaleSigned_eval (s : Nat) (p : SignedTy.denote) :
    scaleSigned.eval (s,p) = encodeInt ((s : Int)*integer p) := by
  change normalize.eval (s*p.1,s*p.2) = _
  rw [normalize_eval]
  congr 1
  simp only [integer,Nat.cast_mul,mul_sub]

abbrev InputTy := Ty.pair .nat (.pair PointTy .bool)

/-- False and true encode phases zero and one, respectively. -/
def frame : Code InputTy FrameTy :=
  let x : Code InputTy SignedTy :=
    .comp (.pair .fst (.comp .snd (.comp .fst .fst))) scaleSigned
  let y : Code InputTy SignedTy :=
    .comp (.pair .fst (.comp .snd (.comp .fst .snd))) scaleSigned
  let dx : Code InputTy SignedTy :=
    .branch (.comp .snd .snd) (.const SignedTy (0,0)) (.const SignedTy (0,1))
  .pair (.const .bool true) (.pair (.const .bool false) (.pair (.const .bool false)
    (.pair (.comp (.pair x dx) addSigned)
      (.comp (.pair y (.const SignedTy (0,1))) addSigned))))

theorem frame_eval (s : Nat) (p : PointTy.denote) (χ : Fin 2) :
    frame.eval (s,p,decide (χ=1)) =
      encodeFrame (NineClusterPlacement.frame s (decoded p) χ) := by
  rcases p with ⟨x,y⟩
  fin_cases χ
  all_goals change (true,false,false,
    (addSigned.eval (scaleSigned.eval (s,x),_),
      addSigned.eval (scaleSigned.eval (s,y),(0,1)))) = _
  all_goals rw [addSigned_eval,addSigned_eval,scaleSigned_eval,scaleSigned_eval,
    integer_encodeInt,integer_encodeInt]
  all_goals simp [encodeFrame,NineClusterPlacement.frame,encodePoint,decoded,integer,Code.eval,sub_eq_add_neg]

def rectangle : Code InputTy RectangleTy :=
  .pair frame (.const (.pair PaddingTy PaddingTy)
    (List.replicate 3 false,List.replicate 3 false))

theorem rectangle_eval (s : Nat) (p : PointTy.denote) (χ : Fin 2) :
    rectangle.eval (s,p,decide (χ=1)) =
      GridAssembly.Rectangles.box (NineClusterPlacement.frame s (decoded p) χ) 3 3 := by
  change (frame.eval (s,p,decide (χ=1)),_) = _
  rw [frame_eval]
  rfl

theorem rectangle_points (s : Nat) (p : PointTy.denote) (χ : Fin 2) :
    GridPointCode.rectanglePoints (rectangle.eval (s,p,decide (χ=1))) =
      NineClusterPlacement.points s (decoded p) χ := by
  rw [rectangle_eval,GridAssembly.Rectangles.box_cluster]
  rfl

/-- A whole family shares the dilation factor and carries a phase per anchor. -/
def family : Code (.pair .nat (.list (.pair PointTy .bool))) GridPointCode.InputTy :=
  .listMapEnv rectangle

theorem family_eval (s : Nat) (ps : List (Point × Fin 2)) :
    family.eval (s,ps.map (fun p => (encodePoint p.1,decide (p.2=1)))) =
      ps.map (fun p => GridAssembly.Rectangles.box
        (NineClusterPlacement.frame s p.1 p.2) 3 3) := by
  change (ps.map _).map (fun p => rectangle.eval (s,p)) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  dsimp only [Function.comp_def]
  rw [rectangle_eval,GridAssembly.Encoding.decode_encode]

end GridHardness.NineClusterCode
