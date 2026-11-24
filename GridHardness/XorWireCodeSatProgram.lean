/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCode
public import GridHardness.PlanarSatCode
public import GridHardness.SatWireExpansion
public import GridHardness.PositiveSat

/-!
# XOR Wire Code SAT Program

Compile outside vertices, crossing cells, and wire stretches from the SAT formula.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorWireCodeSat
open CliffordComplexity PlanarSatAssembly
open XorWireCode (InputTy NatListTy EdgeTy EdgesTy PortTy BoundaryTy LinksTy)

/-- List-bounded copies supply all vertex counts; no binary-sized range is
enumerated by this compiler. -/
def copies {σ τ : Ty} (l : Code σ (.list τ)) (n : Nat) : Code σ NatListTy :=
  .comp l (.comp (.listMap (.const NatListTy (List.replicate n 0))) .listJoin)

theorem copies_length {σ τ : Ty} (l : Code σ (.list τ)) (n : Nat) (x : σ.denote) :
    ((copies l n).eval x).length = (l.eval x).length * n := by
  change ((l.eval x).map (fun _ => List.replicate n 0)).flatten.length = _
  simp [List.length_flatten]

def outerVertices : Code SatTy NatListTy :=
  Code.append (Code.append (.const NatListTy [0,0,0])
    (copies PlanarSatCode.varPool 2)) (copies .id 12)
def cells : Code SatTy NatListTy := copies .id 3
def stretches : Code SatTy NatListTy := copies cells 2
def outerCount : Code SatTy .nat := .comp outerVertices .listLen
def cellCount : Code SatTy .nat := .comp cells .listLen

theorem outerVertices_length (x : SatTy.denote) :
    (outerVertices.eval x).length = 3 + ((vsOf x).length+1)*2 + x.length*12 := by
  change ([0,0,0] ++ (copies PlanarSatCode.varPool 2).eval x ++
    (copies (.id : Code SatTy SatTy) 12).eval x).length = _
  rw [List.length_append,List.length_append,copies_length,copies_length]
  exact congrArg (fun n => 3+n*2+x.length*12) (PlanarSatCode.varCount_eval x)

theorem cells_length (x : SatTy.denote) : (cells.eval x).length = x.length*3 :=
  copies_length .id 3 x
theorem stretches_length (x : SatTy.denote) : (stretches.eval x).length = x.length*6 := by
  rw [stretches,copies_length,cells_length]
  omega

/-- Decide whether the pair is one of the actual SAT-assembly arcs. -/
def hasEdge : Code (.pair SatTy EdgeTy) .bool :=
  .comp (.pair .snd (.comp .fst PlanarSatCode.edgesCode))
    (.comp (Code.isNil (Code.filterEnv Code.natPairEq)) .boolNot)

theorem hasEdge_eval (x : SatTy.denote) (p : Nat ×Nat) :
    hasEdge.eval (x,p) = true ↔ p ∈ PlanarSatCode.edgesCode.eval x := by
  change (!(Code.isNil (Code.filterEnv Code.natPairEq)).eval
    (p,PlanarSatCode.edgesCode.eval x)) = true ↔ _
  rw [Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
  rw [isNil_eval_true (Code.filterEnv (e := EdgeTy) (t := EdgeTy) Code.natPairEq)
    (p,PlanarSatCode.edgesCode.eval x),filterEnv_eval,List.filter_eq_nil_iff]
  simp only [not_forall,not_not,exists_prop,Prod.exists]
  constructor
  · rintro ⟨a,b,hm,he⟩
    exact ((natPairEq_eval_true p (a,b)).mp he).symm ▸ hm
  · intro hp
    exact ⟨p.1,p.2,hp,(natPairEq_eval_true p p).mpr rfl⟩

def outerPairs : Code SatTy EdgesTy :=
  .comp (.pair (.comp outerVertices Code.indices) (.comp outerVertices Code.indices)) Code.cross
def ports : Code SatTy (.list PortTy) :=
  .comp (.pair (.comp cells Code.indices) (.const (.list .bool) [false,true])) Code.cross
def boundaries : Code SatTy (.list BoundaryTy) :=
  .comp (.pair (.comp outerVertices Code.indices) ports) Code.cross
def links : Code SatTy LinksTy := .comp (.pair ports ports) Code.cross

def xorNum {σ : Ty} (env : Code σ SatTy) (c j : Code σ .nat) : Code σ .nat :=
  Code.add (.comp env outerCount) (Code.add (Code.mul c (.const .nat 8)) j)
def entryNum {σ : Ty} (env : Code σ SatTy) (c : Code σ .nat) (s : Code σ .bool) : Code σ .nat :=
  xorNum env c (.branch s (.const .nat 3) (.const .nat 4))
def exitNum {σ : Ty} (env : Code σ SatTy) (c : Code σ .nat) (s : Code σ .bool) : Code σ .nat :=
  xorNum env c (.branch s (.const .nat 0) (.const .nat 7))

abbrev BoundaryAtTy := Ty.pair SatTy BoundaryTy
def boundaryOutside : Code BoundaryAtTy .nat := .comp .snd .fst
def boundaryCell : Code BoundaryAtTy .nat := .comp .snd (.comp .snd .fst)
def boundaryChoice : Code BoundaryAtTy .bool := .comp .snd (.comp .snd .snd)
def enterPair : Code BoundaryAtTy EdgeTy :=
  .pair boundaryOutside (entryNum .fst boundaryCell boundaryChoice)
def leavePair : Code BoundaryAtTy EdgeTy :=
  .pair (exitNum .fst boundaryCell boundaryChoice) boundaryOutside

abbrev LinkAtTy := Ty.pair SatTy (.pair PortTy PortTy)
def linkPair : Code LinkAtTy EdgeTy := .pair
  (exitNum .fst (.comp .snd (.comp .fst .fst)) (.comp .snd (.comp .fst .snd)))
  (entryNum .fst (.comp .snd (.comp .snd .fst)) (.comp .snd (.comp .snd .snd)))

def outerEdges : Code SatTy EdgesTy :=
  .comp (.pair .id outerPairs) (Code.filterEnv hasEdge)
def entering : Code SatTy (.list BoundaryTy) :=
  .comp (.pair .id boundaries) (Code.filterEnv (.comp (.pair .fst enterPair) hasEdge))
def leaving : Code SatTy (.list BoundaryTy) :=
  .comp (.pair .id boundaries) (Code.filterEnv (.comp (.pair .fst leavePair) hasEdge))
def linking : Code SatTy LinksTy :=
  .comp (.pair .id links) (Code.filterEnv (.comp (.pair .fst linkPair) hasEdge))

/-- The explicit SAT occurrence network, with six stretch positions per clause. -/
def assembly : Code SatTy InputTy := .pair
  (.pair outerVertices (.pair outerEdges (.const .nat 0)))
  (.pair cells (.pair stretches (.pair entering (.pair leaving linking))))

theorem mem_outerPairs (x : SatTy.denote) (p : Nat ×Nat) :
    p ∈ outerPairs.eval x ↔ p.1 < (outerVertices.eval x).length ∧
      p.2 < (outerVertices.eval x).length := by
  change p ∈ Code.cross.eval (Code.indices.eval (outerVertices.eval x),
    Code.indices.eval (outerVertices.eval x)) ↔ _
  rw [mem_cross_eval (σ := .nat) (τ := .nat)]
  simp only [indices_eval,List.mem_range]

theorem mem_ports (x : SatTy.denote) (p : Nat ×Bool) :
    p ∈ ports.eval x ↔ p.1 < (cells.eval x).length := by
  change p ∈ (Code.cross (σ := .nat) (τ := .bool)).eval
    (Code.indices.eval (cells.eval x),[false,true]) ↔ _
  rw [mem_cross_eval (σ := .nat) (τ := .bool)]
  cases p.2 <;> simp [indices_eval]

theorem mem_boundaries (x : SatTy.denote) (p : Nat ×(Nat ×Bool)) :
    p ∈ boundaries.eval x ↔ p.1 < (outerVertices.eval x).length ∧
      p.2.1 < (cells.eval x).length := by
  change p ∈ Code.cross.eval (Code.indices.eval (outerVertices.eval x),ports.eval x) ↔ _
  rw [mem_cross_eval (σ := .nat) (τ := PortTy),mem_ports]
  simp only [indices_eval,List.mem_range]

theorem mem_links (x : SatTy.denote) (p : (Nat ×Bool) ×(Nat ×Bool)) :
    p ∈ links.eval x ↔ p.1.1 < (cells.eval x).length ∧
      p.2.1 < (cells.eval x).length := by
  change p ∈ Code.cross.eval (ports.eval x,ports.eval x) ↔ _
  rw [mem_cross_eval (σ := PortTy) (τ := PortTy),mem_ports,mem_ports]

theorem mem_outerEdges (x : SatTy.denote) (p : Nat ×Nat) :
    p ∈ outerEdges.eval x ↔
      (p.1 < (outerVertices.eval x).length ∧ p.2 < (outerVertices.eval x).length) ∧
      p ∈ PlanarSatCode.edgesCode.eval x := by
  change p ∈ (Code.filterEnv hasEdge).eval (x,outerPairs.eval x) ↔ _
  rw [filterEnv_eval,List.mem_filter,mem_outerPairs,hasEdge_eval]

theorem mem_entering (x : SatTy.denote) (p : Nat ×(Nat ×Bool)) :
    p ∈ entering.eval x ↔
      (p.1 < (outerVertices.eval x).length ∧ p.2.1 < (cells.eval x).length) ∧
      enterPair.eval (x,p) ∈ PlanarSatCode.edgesCode.eval x := by
  change p ∈ (Code.filterEnv (.comp (.pair .fst enterPair) hasEdge)).eval
    (x,boundaries.eval x) ↔ _
  rw [filterEnv_eval,List.mem_filter,mem_boundaries]
  change _ ∧ hasEdge.eval (x,enterPair.eval (x,p)) = true ↔ _
  rw [hasEdge_eval]

theorem mem_leaving (x : SatTy.denote) (p : Nat ×(Nat ×Bool)) :
    p ∈ leaving.eval x ↔
      (p.1 < (outerVertices.eval x).length ∧ p.2.1 < (cells.eval x).length) ∧
      leavePair.eval (x,p) ∈ PlanarSatCode.edgesCode.eval x := by
  change p ∈ (Code.filterEnv (.comp (.pair .fst leavePair) hasEdge)).eval
    (x,boundaries.eval x) ↔ _
  rw [filterEnv_eval,List.mem_filter,mem_boundaries]
  change _ ∧ hasEdge.eval (x,leavePair.eval (x,p)) = true ↔ _
  rw [hasEdge_eval]

theorem mem_linking (x : SatTy.denote) (p : (Nat ×Bool) ×(Nat ×Bool)) :
    p ∈ linking.eval x ↔
      (p.1.1 < (cells.eval x).length ∧ p.2.1 < (cells.eval x).length) ∧
      linkPair.eval (x,p) ∈ PlanarSatCode.edgesCode.eval x := by
  change p ∈ (Code.filterEnv (.comp (.pair .fst linkPair) hasEdge)).eval
    (x,links.eval x) ↔ _
  rw [filterEnv_eval,List.mem_filter,mem_links]
  change _ ∧ hasEdge.eval (x,linkPair.eval (x,p)) = true ↔ _
  rw [hasEdge_eval]

end GridHardness.XorWireCodeSat
