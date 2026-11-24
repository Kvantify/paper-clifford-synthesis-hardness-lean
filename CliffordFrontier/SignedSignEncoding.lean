/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap

/-!
# Signed Sign Encoding

Polynomial-time operations on the Boolean sign vectors of a signed tableau.
-/

@[expose] public section

namespace CliffordFrontier

open Turing.MultiTapeTM

theorem readSign_polyTime :
    ComputableInPolyTime (fun p : List Bool × Nat => p.1[p.2]?.getD false)
      (encPair (encList encBool) encUnary) encBool := by
  simpa only [List.getD_eq_getElem?_getD] using
    (ComputableInPolyTime.listGetD (encA := encBool) (encL := encList encBool) false)

theorem tabulateSigns_polyTime {α : Type} {enc : α ↪ List Bool} {n : α → Nat}
    {f : α → Nat → Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hf : ComputableInPolyTime (fun q : α × Nat => f q.1 q.2)
      (encPair enc encUnary) encBool) :
    ComputableInPolyTime (fun x => (List.range (n x)).map (f x)) enc (encList encBool) :=
  ComputableInPolyTime.mapWithInput (ComputableInPolyTime.unary_range' hn) hf

/-- Compare the first `n` entries, interpreting missing signs as positive. -/
def compareSigns (n : Nat) (a b : List Bool) : Bool :=
  (List.range n).all fun i => decide (a[i]?.getD false = b[i]?.getD false)

theorem compareSigns_iff (n : Nat) (a b : List Bool) :
    compareSigns n a b = true ↔ ∀ i < n, a[i]?.getD false = b[i]?.getD false := by
  simp only [compareSigns, List.all_eq_true, List.mem_range, decide_eq_true_eq]

theorem compareSigns_polyTime :
    ComputableInPolyTime (fun x : Nat × List Bool × List Bool => compareSigns x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair (encList encBool) (encList encBool))) encBool := by
  let encSigns := encList encBool
  let encInput := encPair encUnary (encPair encSigns encSigns)
  let input := ComputableInPolyTime.fst encInput encUnary
  let index := ComputableInPolyTime.snd encInput encUnary
  have readLeft := readSign_polyTime.comp (input.snd'.fst'.prod index)
  have readRight := readSign_polyTime.comp (input.snd'.snd'.prod index)
  exact ComputableInPolyTime.allWithInput
    (ComputableInPolyTime.unary_range' (ComputableInPolyTime.fst encUnary (encPair encSigns encSigns)))
    (readLeft.decide_eq' readRight)

end CliffordFrontier
