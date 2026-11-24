/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyEncoding
public import CliffordComplexity.ListPrograms
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Foundations.Data.List.EraseDupsBy

/-!
# Grid Point Code

A certified coordinate-set builder. Rectangle side lengths are given by
explicit padding lists, while origins are arbitrary signed binary integers.
All enumeration is over input list positions. Overlapping rectangles are
allowed: canonical coordinates and certified deduplication form their union.
-/

@[expose] public section

namespace GridHardness.GridPointCode
open CliffordSynthesis SimpleGraph OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode
open Turing.MultiTapeTM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev PaddingTy := Ty.list .bool
abbrev FrameTy := Ty.pair .bool (.pair .bool (.pair .bool PointTy))
abbrev RectangleTy := Ty.pair FrameTy (.pair PaddingTy PaddingTy)
abbrev InputTy := Ty.list RectangleTy

instance frameDecidableEq : DecidableEq FrameTy.denote := by
  change DecidableEq (Bool × Bool × Bool × ((Nat × Nat) × (Nat × Nat)))
  infer_instance

instance rectangleDecidableEq : DecidableEq RectangleTy.denote := by
  change DecidableEq (FrameTy.denote × List Bool × List Bool)
  infer_instance

def decodeFrame (f : FrameTy.denote) : Frame := ⟨f.1, f.2.1, f.2.2.1, decoded f.2.2.2⟩

def encodeFrame (f : Frame) : FrameTy.denote :=
  (f.horizontal, f.reverseX, f.reverseY, encodePoint f.origin)

@[simp] theorem decode_encodeFrame (f : Frame) : decodeFrame (encodeFrame f) = f := by
  cases f
  simp [decodeFrame, encodeFrame, GridAssembly.Encoding.decode_encode]

/-- Canonical positive/negative parts of a possibly redundant signed pair. -/
def normalize : Code SignedTy SignedTy :=
  .pair (.comp (.pair .fst .snd) .natSub) (.comp (.pair .snd .fst) .natSub)

theorem normalize_eval (p : SignedTy.denote) : normalize.eval p = encodeInt (integer p) := by
  rcases p with ⟨a, b⟩
  simp [normalize, Code.eval, encodeInt, integer]

def addSigned : Code (.pair SignedTy SignedTy) SignedTy :=
  .comp (.pair (Code.add (.comp .fst .fst) (.comp .snd .fst))
    (Code.add (.comp .fst .snd) (.comp .snd .snd))) normalize

theorem addSigned_eval (p q : SignedTy.denote) :
    addSigned.eval (p, q) = encodeInt (integer p + integer q) := by
  change normalize.eval (p.1 + q.1, p.2 + q.2) = _
  rw [normalize_eval]
  congr 1
  simp only [integer, Nat.cast_add]
  omega

def signedNat : Code (.pair .bool .nat) SignedTy :=
  .branch .fst (.pair (.const .nat 0) .snd) (.pair .snd (.const .nat 0))

theorem signedNat_eval (b : Bool) (n : Nat) :
    signedNat.eval (b, n) = encodeInt (sign b (n : Int)) := by
  cases b <;> simp [signedNat, Code.eval, encodeInt, sign]

/-- Affine orthogonal coordinates, normalized to the canonical signed form. -/
def pointAt : Code (.pair FrameTy (.pair .nat .nat)) PointTy :=
  let h : Code (.pair FrameTy (.pair .nat .nat)) .bool := .comp .fst .fst
  let rx := .comp .fst (.comp .snd .fst)
  let ry := .comp .fst (.comp .snd (.comp .snd .fst))
  let origin : Code (.pair FrameTy (.pair .nat .nat)) PointTy :=
    .comp .fst (.comp .snd (.comp .snd .snd))
  let u := .comp (.pair rx (.comp .snd .fst)) signedNat
  let v := .comp (.pair ry (.comp .snd .snd)) signedNat
  .pair (.comp (.pair (.comp origin .fst) (.branch h u v)) addSigned)
    (.comp (.pair (.comp origin .snd) (.branch h v u)) addSigned)

theorem pointAt_eval (f : FrameTy.denote) (i j : Nat) :
    pointAt.eval (f, (i, j)) = encodePoint ((decodeFrame f).map (i, j)) := by
  rcases f with ⟨h, rx, ry, x, y⟩
  cases h <;>
    simp only [pointAt, Code.eval, Bool.false_eq_true, ite_false, ite_true,
      decodeFrame, Frame.map, place, encodePoint, decoded]
  all_goals rw [addSigned_eval, addSigned_eval, signedNat_eval, signedNat_eval,
    integer_encodeInt, integer_encodeInt]

def rectangle : Code RectangleTy CycleInputTy :=
  .comp (.pair .fst
    (.comp (.pair (.comp (.comp .snd .fst) Code.indices)
      (.comp (.comp .snd .snd) Code.indices)) Code.cross)) (.listMapEnv pointAt)

/-- The exact finite coordinate rectangle described by the two paddings. -/
def rectanglePoints (r : RectangleTy.denote) : Finset Point :=
  ((Finset.range r.2.1.length).product (Finset.range r.2.2.length)).image
    (fun q => (decodeFrame r.1).map (q.1, q.2))

theorem rectangle_mem (r : RectangleTy.denote) (p : PointTy.denote) :
    p ∈ rectangle.eval r ↔ ∃ q ∈ rectanglePoints r, p = encodePoint q := by
  change p ∈ (Code.cross.eval (Code.indices.eval r.2.1, Code.indices.eval r.2.2)).map
    (fun q => pointAt.eval (r.1, q)) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    have hij := (mem_cross_eval (σ := .nat) (τ := .nat) _ _ _).mp hij
    simp only [indices_eval, List.mem_range] at hij
    refine ⟨_, Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hij.1, Finset.mem_range.mpr hij.2⟩, rfl⟩, ?_⟩
    exact pointAt_eval _ _ _
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hq
    have hij := Finset.mem_product.mp hij
    refine ⟨(i, j), ?_, pointAt_eval _ _ _⟩
    apply (mem_cross_eval (σ := .nat) (τ := .nat) _ _ _).mpr
    simpa only [indices_eval, List.mem_range, Finset.mem_range] using hij

def raw : Code InputTy CycleInputTy := .comp (.listMap rectangle) .listJoin

def code : Code InputTy CycleInputTy :=
  .ofPolyTime (fun rs => (raw.eval rs).eraseDupsBy fun a b => decide (a = b))
    (ComputableInPolyTime.eraseDupsByWithInput raw.polyTime
      (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst _ _).snd'
        (ComputableInPolyTime.snd _ _)))

theorem code_eval (rs : InputTy.denote) :
    code.eval rs = (raw.eval rs).eraseDupsBy (fun a b => decide (a = b)) := rfl

def points (rs : InputTy.denote) : Finset Point := rs.toFinset.biUnion rectanglePoints

theorem code_mem (rs : InputTy.denote) (p : PointTy.denote) :
    p ∈ code.eval rs ↔ ∃ q ∈ points rs, p = encodePoint q := by
  rw [code_eval, List.mem_eraseDupsBy_eq]
  change p ∈ (rs.map (rectangle.eval ·)).flatten ↔ _
  constructor
  · intro hp
    obtain ⟨xs, hxs, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hxs
    obtain ⟨q, hq, hp⟩ := (rectangle_mem r p).mp hp
    exact ⟨q, Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, hq⟩, hp⟩
  · rintro ⟨q, hq, hp⟩
    obtain ⟨r, hr, hq⟩ := Finset.mem_biUnion.mp hq
    apply List.mem_flatten.mpr
    exact ⟨rectangle.eval r, List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩,
      (rectangle_mem r p).mpr ⟨q, hq, hp⟩⟩

theorem code_canonical (rs : InputTy.denote) (p : PointTy.denote) (hp : p ∈ code.eval rs) :
    encodePoint (decoded p) = p := by
  obtain ⟨q, _, rfl⟩ := (code_mem rs p).mp hp
  rw [GridAssembly.Encoding.decode_encode]

theorem code_nodup (rs : InputTy.denote) : (code.eval rs).Nodup := by
  rw [code_eval]
  exact List.nodup_eraseDupsBy_eq _

theorem code_decoded_nodup (rs : InputTy.denote) : ((code.eval rs).map decoded).Nodup := by
  apply List.Nodup.map_on _ (code_nodup rs)
  intro p hp q hq he
  rw [← code_canonical rs p hp, ← code_canonical rs q hq, he]

theorem code_decoded_mem (rs : InputTy.denote) (q : Point) :
    q ∈ (code.eval rs).map decoded ↔ q ∈ points rs := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := (code_mem rs p).mp hp
    simpa only [GridAssembly.Encoding.decode_encode] using hq
  · intro hq
    exact ⟨encodePoint q, (code_mem rs _).mpr ⟨q, hq, rfl⟩,
      GridAssembly.Encoding.decode_encode q⟩

end GridHardness.GridPointCode
