/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCodeProgram

/-!
# XOR Wire Code Eval

Evaluation rules for compiled XOR wire edges, boundary links, and outside checks.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 2000000

namespace GridHardness.XorWireCode
open CliffordComplexity

def inNum (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Nat) (b : Bool) : Nat :=
  if b then wireNum x.1.1.length (L.eval x).length c 0 3
    else wireNum x.1.1.length (L.eval x).length c (L.eval x).length 4

def outNum (L : Code InputTy NatListTy) (x : InputTy.denote) (c : Nat) (b : Bool) : Nat :=
  if b then wireNum x.1.1.length (L.eval x).length c (L.eval x).length 0
    else wireNum x.1.1.length (L.eval x).length c 0 7

theorem internalAt_eval (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × Nat) :
    (internalAt L).eval (x,p) = (List.finRange 10).map (fun e =>
      (wireNum x.1.1.length (L.eval x).length p.1 p.2 (XorGadget.arc e).1.val,
       wireNum x.1.1.length (L.eval x).length p.1 p.2 (XorGadget.arc e).2.val)) := by
  rw [internalAt, tableEdges_eval]
  rfl

theorem wireLinkAt_eval (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × Nat) :
    (wireLinkAt L).eval (x,p) =
      [(wireNum x.1.1.length (L.eval x).length p.1 p.2 0,
        wireNum x.1.1.length (L.eval x).length p.1 (p.2+1) 3),
       (wireNum x.1.1.length (L.eval x).length p.1 (p.2+1) 7,
        wireNum x.1.1.length (L.eval x).length p.1 p.2 4)] := rfl

theorem outsideValid_eval (x : InputTy.denote) (p : Nat × Nat) :
    outsideValid.eval (x,p) = true ↔ p.1 < x.1.1.length ∧ p.2 < x.1.1.length := by
  change (Code.natLt.eval (p.1,x.1.1.length) && Code.natLt.eval (p.2,x.1.1.length)) = true ↔ _
  rw [Bool.and_eq_true, natLt_eval_true, natLt_eval_true]

theorem boundaryValid_eval (x : InputTy.denote) (p : Nat × (Nat × Bool)) :
    boundaryValid.eval (x,p) = true ↔ p.1 < x.1.1.length ∧ p.2.1 < x.2.1.length := by
  change (Code.natLt.eval (p.1,x.1.1.length) && Code.natLt.eval (p.2.1,x.2.1.length)) = true ↔ _
  rw [Bool.and_eq_true, natLt_eval_true, natLt_eval_true]

theorem linkValid_eval (x : InputTy.denote) (p : (Nat × Bool) × (Nat × Bool)) :
    linkValid.eval (x,p) = true ↔
      (p.1.1 < x.2.1.length ∧ p.2.1 < x.2.1.length) ∧ p.1.1 ≠ p.2.1 := by
  change ((Code.natLt.eval (p.1.1,x.2.1.length) &&
    Code.natLt.eval (p.2.1,x.2.1.length)) && !decide (p.1.1 = p.2.1)) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, natLt_eval_true, natLt_eval_true]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]

theorem enterAt_eval (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × (Nat × Bool)) :
    (enterAt L).eval (x,p) = (p.1,inNum L x p.2.1 p.2.2) := rfl

theorem leaveAt_eval (L : Code InputTy NatListTy) (x : InputTy.denote) (p : Nat × (Nat × Bool)) :
    (leaveAt L).eval (x,p) = (outNum L x p.2.1 p.2.2,p.1) := rfl

theorem linkAt_eval (L : Code InputTy NatListTy) (x : InputTy.denote)
    (p : (Nat × Bool) × (Nat × Bool)) :
    (linkAt L).eval (x,p) = (outNum L x p.1.1 p.1.2,inNum L x p.2.1 p.2.2) := rfl

theorem mem_outsideCode (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ outsideCode.eval x ↔ q ∈ x.1.2.1 ∧ q.1 < x.1.1.length ∧ q.2 < x.1.1.length := by
  change q ∈ (Code.filterEnv outsideValid).eval (x,x.1.2.1) ↔ _
  rw [filterEnv_eval, List.mem_filter, outsideValid_eval]

theorem mem_internalCode (L : Code InputTy NatListTy) (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ (internalCode L).eval x ↔ ∃ p : Nat × Nat,
      (p.1 < x.2.1.length ∧ p.2 < (L.eval x).length + 1) ∧ ∃ e : Fin 10,
      (wireNum x.1.1.length (L.eval x).length p.1 p.2 (XorGadget.arc e).1.val,
       wireNum x.1.1.length (L.eval x).length p.1 p.2 (XorGadget.arc e).2.val) = q := by
  change q ∈ ((cellSections L).eval x).flatMap (fun p => (internalAt L).eval (x,p)) ↔ _
  rw [List.mem_flatMap]
  apply exists_congr
  intro p
  rw [mem_cellSections, internalAt_eval]
  simp only [List.mem_map, List.mem_finRange, true_and]

theorem mem_wireLinksCode (L : Code InputTy NatListTy) (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ (wireLinksCode L).eval x ↔ ∃ p : Nat × Nat,
      (p.1 < x.2.1.length ∧ p.2 < (L.eval x).length) ∧
      (q = (wireNum x.1.1.length (L.eval x).length p.1 p.2 0,
         wireNum x.1.1.length (L.eval x).length p.1 (p.2+1) 3) ∨
       q = (wireNum x.1.1.length (L.eval x).length p.1 (p.2+1) 7,
         wireNum x.1.1.length (L.eval x).length p.1 p.2 4)) := by
  change q ∈ ((cellLinks L).eval x).flatMap (fun p => (wireLinkAt L).eval (x,p)) ↔ _
  rw [List.mem_flatMap]
  apply exists_congr
  intro p
  rw [mem_cellLinks, wireLinkAt_eval]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem mem_enterCode (L : Code InputTy NatListTy) (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ (enterCode L).eval x ↔ ∃ p ∈ x.2.2.2.1,
      (p.1 < x.1.1.length ∧ p.2.1 < x.2.1.length) ∧ (p.1,inNum L x p.2.1 p.2.2) = q := by
  change q ∈ (Code.filterMapEnv boundaryValid (enterAt L)).eval (x,x.2.2.2.1) ↔ _
  rw [mem_filterMapEnv_eval]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  rw [boundaryValid_eval, enterAt_eval]

theorem mem_leaveCode (L : Code InputTy NatListTy) (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ (leaveCode L).eval x ↔ ∃ p ∈ x.2.2.2.2.1,
      (p.1 < x.1.1.length ∧ p.2.1 < x.2.1.length) ∧ (outNum L x p.2.1 p.2.2,p.1) = q := by
  change q ∈ (Code.filterMapEnv boundaryValid (leaveAt L)).eval (x,x.2.2.2.2.1) ↔ _
  rw [mem_filterMapEnv_eval]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  rw [boundaryValid_eval, leaveAt_eval]

theorem mem_linksCode (L : Code InputTy NatListTy) (x : InputTy.denote) (q : Nat × Nat) :
    q ∈ (linksCode L).eval x ↔ ∃ p ∈ x.2.2.2.2.2,
      ((p.1.1 < x.2.1.length ∧ p.2.1 < x.2.1.length) ∧ p.1.1 ≠ p.2.1) ∧
      (outNum L x p.1.1 p.1.2,inNum L x p.2.1 p.2.2) = q := by
  change q ∈ (Code.filterMapEnv linkValid (linkAt L)).eval (x,x.2.2.2.2.2) ↔ _
  rw [mem_filterMapEnv_eval]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  rw [linkValid_eval, linkAt_eval]

end GridHardness.XorWireCode
