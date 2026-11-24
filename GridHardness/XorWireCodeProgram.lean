/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireNetwork
public import GridHardness.DirectedToBipartiteCode
public import CliffordComplexity.Numbering

/-!
# XOR Wire Code Program

Polynomial-time constructors for the numbered vertices and edges of XOR wire replacements.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorWireCode
open CliffordComplexity

abbrev NatListTy := Ty.list .nat
abbrev EdgeTy := Ty.pair .nat .nat
abbrev EdgesTy := Ty.list EdgeTy
abbrev PortTy := Ty.pair .nat .bool
abbrev BoundaryTy := Ty.pair .nat PortTy
abbrev LinksTy := Ty.list (.pair PortTy PortTy)
/-- Outside graph, explicit cell list, explicit extension-length list,
entering links, leaving links, and links between cells. Boundary links store
an outside position followed by a cell position and a Boolean port choice. -/
abbrev InputTy := Ty.pair GraphTy (.pair NatListTy (.pair NatListTy
  (.pair (.list BoundaryTy) (.pair (.list BoundaryTy) LinksTy))))

def outerVertices : Code InputTy NatListTy := .comp .fst .fst
def outerEdges : Code InputTy EdgesTy := .comp .fst (.comp .snd .fst)
def cells : Code InputTy NatListTy := .comp .snd .fst
def stretches : Code InputTy NatListTy := .comp .snd (.comp .snd .fst)
def entering : Code InputTy (.list BoundaryTy) := .comp .snd (.comp .snd (.comp .snd .fst))
def leaving : Code InputTy (.list BoundaryTy) := .comp .snd (.comp .snd (.comp .snd (.comp .snd .fst)))
def linking : Code InputTy LinksTy := .comp .snd (.comp .snd (.comp .snd (.comp .snd .snd)))
def outerCount : Code InputTy .nat := .comp outerVertices .listLen
def cellCount : Code InputTy .nat := .comp cells .listLen

def wireNum (o n c s j : Nat) : Nat := o + (c * ((n + 1) * 8) + (s * 8 + j))

def numWire {σ : Ty} (L : Code InputTy NatListTy) (env : Code σ InputTy)
    (c s j : Code σ .nat) : Code σ .nat :=
  Code.add (.comp env outerCount)
    (Code.add (Code.mul c (Code.mul (Code.add (.comp env (.comp L .listLen))
      (.const .nat 1)) (.const .nat 8)))
      (Code.add (Code.mul s (.const .nat 8)) j))

theorem numWire_eval {σ : Ty} (L : Code InputTy NatListTy) (env : Code σ InputTy)
    (c s j : Code σ .nat) (a : σ.denote) :
    (numWire L env c s j).eval a = wireNum (env.eval a).1.1.length
      (L.eval (env.eval a)).length (c.eval a) (s.eval a) (j.eval a) := rfl

def inputNum {σ : Ty} (L : Code InputTy NatListTy) (env : Code σ InputTy)
    (c : Code σ .nat) (s : Code σ .bool) : Code σ .nat :=
  .branch s (numWire L env c (.const .nat 0) (.const .nat 3))
    (numWire L env c (.comp env (.comp L .listLen)) (.const .nat 4))

def outputNum {σ : Ty} (L : Code InputTy NatListTy) (env : Code σ InputTy)
    (c : Code σ .nat) (s : Code σ .bool) : Code σ .nat :=
  .branch s (numWire L env c (.comp env (.comp L .listLen)) (.const .nat 0))
    (numWire L env c (.const .nat 0) (.const .nat 7))

def cellSections (L : Code InputTy NatListTy) : Code InputTy (.list EdgeTy) :=
  .comp (.pair (.comp cells Code.indices)
    (.comp (Code.cons (.const .nat 0) L) Code.indices)) Code.cross

def cellLinks (L : Code InputTy NatListTy) : Code InputTy (.list EdgeTy) :=
  .comp (.pair (.comp cells Code.indices) (.comp L Code.indices)) Code.cross

theorem mem_cellSections (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × Nat) :
    p ∈ (cellSections L).eval x ↔ p.1 < x.2.1.length ∧ p.2 < (L.eval x).length + 1 := by
  change p ∈ Code.cross.eval (Code.indices.eval x.2.1, Code.indices.eval (0 :: L.eval x)) ↔ _
  rw [mem_cross_eval (σ := .nat) (τ := .nat)]
  simp only [indices_eval, List.mem_range, List.length_cons]

theorem mem_cellLinks (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × Nat) :
    p ∈ (cellLinks L).eval x ↔ p.1 < x.2.1.length ∧ p.2 < (L.eval x).length := by
  change p ∈ Code.cross.eval (Code.indices.eval x.2.1, Code.indices.eval (L.eval x)) ↔ _
  rw [mem_cross_eval (σ := .nat) (τ := .nat)]
  simp only [indices_eval, List.mem_range]

def vertices (L : Code InputTy NatListTy) : Code InputTy NatListTy :=
  Code.append outerVertices (.comp (cellSections L)
    (.comp (.listMap (.const NatListTy (List.replicate 8 0))) .listJoin))

theorem vertices_length (L : Code InputTy NatListTy) (x : InputTy.denote) :
    ((vertices L).eval x).length = x.1.1.length + x.2.1.length * (((L.eval x).length + 1) * 8) := by
  change (x.1.1 ++ (((cellSections L).eval x).map (fun _ => List.replicate 8 0)).flatten).length = _
  have hr (l : List (Nat × Nat)) :
      (l.map (fun _ => List.replicate 8 0)).flatten.length = l.length * 8 := by
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih, Nat.add_mul, Nat.add_comm] <;> omega
  rw [List.length_append, hr]
  change x.1.1.length + (Code.cross.eval (Code.indices.eval x.2.1,
    Code.indices.eval (0 :: L.eval x))).length * 8 = _
  rw [length_cross_eval (σ := .nat) (τ := .nat), indices_eval, indices_eval]
  simp only [List.length_range, List.length_cons]
  rw [Nat.mul_assoc]

def tableEdges {A : Type*} {σ : Ty} (xs : List A) (f : A → Code σ EdgeTy) : Code σ EdgesTy :=
  xs.foldr (fun a rest => Code.append (.comp (f a) .listSingle) rest) (.const EdgesTy [])

theorem tableEdges_eval {A : Type*} {σ : Ty} (xs : List A) (f : A → Code σ EdgeTy)
    (x : σ.denote) : (tableEdges xs f).eval x = xs.map (fun a => (f a).eval x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (f a).eval x :: (tableEdges xs f).eval x = _
    rw [ih]
    rfl

abbrev AtTy := Ty.pair InputTy EdgeTy
def atCell : Code AtTy .nat := .comp .snd .fst
def atSection : Code AtTy .nat := .comp .snd .snd

def internalAt (L : Code InputTy NatListTy) : Code AtTy EdgesTy :=
  tableEdges (List.finRange 10) (fun e => .pair
    (numWire L .fst atCell atSection (.const .nat (XorGadget.arc e).1.val))
    (numWire L .fst atCell atSection (.const .nat (XorGadget.arc e).2.val)))

def wireLinkAt (L : Code InputTy NatListTy) : Code AtTy EdgesTy :=
  Code.append (.comp (.pair
      (numWire L .fst atCell atSection (.const .nat 0))
      (numWire L .fst atCell (Code.add atSection (.const .nat 1)) (.const .nat 3))) .listSingle)
    (.comp (.pair
      (numWire L .fst atCell (Code.add atSection (.const .nat 1)) (.const .nat 7))
      (numWire L .fst atCell atSection (.const .nat 4))) .listSingle)

def internalCode (L : Code InputTy NatListTy) : Code InputTy EdgesTy :=
  .comp (.pair .id (cellSections L)) (.comp (.listMapEnv (internalAt L)) .listJoin)

def wireLinksCode (L : Code InputTy NatListTy) : Code InputTy EdgesTy :=
  .comp (.pair .id (cellLinks L)) (.comp (.listMapEnv (wireLinkAt L)) .listJoin)

def outsideValid : Code AtTy .bool :=
  Code.and (Code.lt atCell (.comp .fst outerCount)) (Code.lt atSection (.comp .fst outerCount))

def outsideCode : Code InputTy EdgesTy :=
  .comp (.pair .id outerEdges) (Code.filterEnv outsideValid)

abbrev BoundaryAtTy := Ty.pair InputTy BoundaryTy
def boundaryOutside : Code BoundaryAtTy .nat := .comp .snd .fst
def boundaryCell : Code BoundaryAtTy .nat := .comp .snd (.comp .snd .fst)
def boundaryChoice : Code BoundaryAtTy .bool := .comp .snd (.comp .snd .snd)

def boundaryValid : Code BoundaryAtTy .bool :=
  Code.and (Code.lt boundaryOutside (.comp .fst outerCount))
    (Code.lt boundaryCell (.comp .fst cellCount))

def enterAt (L : Code InputTy NatListTy) : Code BoundaryAtTy EdgeTy :=
  .pair boundaryOutside (inputNum L .fst boundaryCell boundaryChoice)
def leaveAt (L : Code InputTy NatListTy) : Code BoundaryAtTy EdgeTy :=
  .pair (outputNum L .fst boundaryCell boundaryChoice) boundaryOutside

def enterCode (L : Code InputTy NatListTy) : Code InputTy EdgesTy :=
  .comp (.pair .id entering) (Code.filterMapEnv boundaryValid (enterAt L))
def leaveCode (L : Code InputTy NatListTy) : Code InputTy EdgesTy :=
  .comp (.pair .id leaving) (Code.filterMapEnv boundaryValid (leaveAt L))

abbrev LinkAtTy := Ty.pair InputTy (.pair PortTy PortTy)
def fromCell : Code LinkAtTy .nat := .comp .snd (.comp .fst .fst)
def fromChoice : Code LinkAtTy .bool := .comp .snd (.comp .fst .snd)
def toCell : Code LinkAtTy .nat := .comp .snd (.comp .snd .fst)
def toChoice : Code LinkAtTy .bool := .comp .snd (.comp .snd .snd)

def linkValid : Code LinkAtTy .bool :=
  Code.and (Code.and (Code.lt fromCell (.comp .fst cellCount))
    (Code.lt toCell (.comp .fst cellCount)))
    (.comp (.comp (.pair fromCell toCell) .natEq) .boolNot)

def linkAt (L : Code InputTy NatListTy) : Code LinkAtTy EdgeTy :=
  .pair (outputNum L .fst fromCell fromChoice) (inputNum L .fst toCell toChoice)

def linksCode (L : Code InputTy NatListTy) : Code InputTy EdgesTy :=
  .comp (.pair .id linking) (Code.filterMapEnv linkValid (linkAt L))

def program (L : Code InputTy NatListTy) : Code InputTy GraphTy :=
  .pair (vertices L) (.pair
    (Code.append outsideCode (Code.append (internalCode L) (Code.append (wireLinksCode L)
      (Code.append (enterCode L) (Code.append (leaveCode L) (linksCode L))))))
    (.const .nat 0))

end GridHardness.XorWireCode
