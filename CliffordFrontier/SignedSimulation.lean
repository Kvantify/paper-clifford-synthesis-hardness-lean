/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedWitness
public import CliffordFrontier.SignedSignEncoding
public import CliffordFrontier.SignedProblem

/-!
# Signed Simulation

Packed tableau simulation for signed Clifford witnesses.
-/

@[expose] public section

namespace CliffordFrontier.SignedVerifier

open Turing.MultiTapeTM CliffordSynthesis

/-- The sign vectors of the X and Z generator images. -/
abbrev Signs := List Bool × List Bool
/-- The packed linear tableau and generator signs of a simulator state. -/
abbrev SignedState := PackedTableau × Signs

/-- Encode the two generator sign vectors as a framed pair. -/
abbrev encSigns : Signs ↪ List Bool := encPair (encList encBool) (encList encBool)
/-- Encode the packed linear tableau followed by the generator sign vectors. -/
abbrev encSignedState : SignedState ↪ List Bool := encPair encPackedTableau encSigns

/-- Interpret the simulated blocks and signs as a signed tableau at a fixed width. -/
def asTableau (n : Nat) (s : SignedState) : SignedCircuit.Tableau n where
  linear := asPackedTableau n s.1
  sign p := (if p.2 then s.2.2 else s.2.1)[p.1.val]?.getD false

/-- The simulation starts in the identity tableau with positive generator signs. -/
def initial (n : Nat) : SignedState :=
  (identityPacked n, List.replicate n false, List.replicate n false)

/-- Extract the packed blocks and generator signs of the requested target. -/
def target (out : SignedInput) : SignedState := (FullVerifier.targetPacked out.1, out.2)

/-- Reduce a local frame number modulo the number of single-qubit frames. -/
def frame (k : Nat) : Fin 6 := ⟨k % 6, Nat.mod_lt _ (by decide)⟩

/-- The six local frames on the first wire, leaving the second wire alone. -/
def frameMatrix (f : Fin 6) : TwoQubit.Matrix :=
  ![33825, 33810, 33841, 33842, 33811, 33827] f

theorem frameMatrix_action : ∀ (f : Fin 6) (v : TwoQubit.Bits),
    TwoQubit.action (frameMatrix f) v = TwoQubit.localAction f 0 v := by decide

/-- Read the symplectic action of a raw signed instruction. -/
def matrix (g : RawStep) : TwoQubit.Matrix :=
  if g.1.1 then BitVec.ofNat 16 g.2.2.1 else frameMatrix (frame g.2.2.1)

/-- Whether the instruction tag denotes a free SWAP. -/
def swapping (g : RawStep) : Bool := g.1.1 && g.1.2

/-- A local frame acts through the first pair of matrix outputs. -/
def indices (g : RawStep) : CNOTIndices :=
  if g.1.1 then g.2.1 else (g.2.1.1, g.2.1.1)

/-- Update the packed linear blocks under one raw signed instruction. -/
def linearStep (s : PackedTableau) (g : RawStep) : PackedTableau :=
  (FullVerifier.applyPairBlocks (s.1, indices g, swapping g, matrix g),
    FullVerifier.applyPairBlocks (s.2, indices g, swapping g, matrix g))

/-- Compute the new sign of one Pauli generator image. -/
def signAfter (s : Blocks × List Bool) (g : RawStep) (j : Nat) : Bool :=
  let previous := s.2[j]?.getD false
  let (c, t) := g.2.1
  let v := (entry s.1.1 c j, entry s.1.2 c j, g.1.1 && entry s.1.1 t j,
    g.1.1 && entry s.1.2 t j)
  if swapping g then previous
  else previous ^^ SignedCircuit.signChange (TwoQubit.action (matrix g)) g.2.2.2 v

/-- Update the sign vector for one of the two kinds of Pauli generators. -/
def signStep (s : Blocks × List Bool) (g : RawStep) : List Bool :=
  (List.range s.1.1.length).map (signAfter s g)

/-- Update both the linear tableau and the signs under one raw instruction. -/
def applyRawStep (p : SignedState × RawStep) : SignedState :=
  (linearStep p.1.1 p.2, signStep (p.1.1.1, p.1.2.1) p.2, signStep (p.1.1.2, p.1.2.2) p.2)

/-- Check all linear entries and both generator sign vectors at the given width. -/
def compare (n : Nat) (s t : SignedState) : Bool :=
  comparePacked n s.1 t.1 && compareSigns n s.2.1 t.2.1 && compareSigns n s.2.2 t.2.2

end CliffordFrontier.SignedVerifier
