/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.MatrixAdequacy

/-!
# Encoding

The dense encoding of block-diagonal tableaus and correctness of the program that
compiles the three-block matrix into that encoding.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CliffordSynthesis.MatrixCompiler
open Planes (F)

/-- Explicit dense encoding of a linear tableau and a binary threshold. -/
def encode {n : Nat} (a : Circuit.Tableau n) (k : Nat) : OutputTy.denote :=
  (List.ofFn (fun i => List.ofFn (fun j => a.x i (j, false))),
   (List.ofFn (fun i => List.ofFn (fun j => a.z i (j, true))), k))

theorem instance_ext (a b : GridInstance.Instance) (hn : a.qubits = b.qubits)
    (hk : a.threshold = b.threshold)
    (hx : ∀ i p, a.tableau.x i p = b.tableau.x (Fin.cast hn i) (Fin.cast hn p.1, p.2))
    (hz : ∀ i p, a.tableau.z i p = b.tableau.z (Fin.cast hn i) (Fin.cast hn p.1, p.2)) : a = b := by
  rcases a with ⟨n, ⟨ax, az⟩, k⟩
  rcases b with ⟨n', ⟨bx, bz⟩, k'⟩
  dsimp at hn hk
  subst n'
  subst k'
  have hxx : ax = bx := funext (fun i => funext (fun p => hx i p))
  have hzz : az = bz := funext (fun i => funext (fun p => hz i p))
  cases hxx
  cases hzz
  rfl

theorem decode_encode {n : Nat} (a : Circuit.Tableau n) (k : Nat)
    (hx : ∀ i j, a.x i (j, true) = false) (hz : ∀ i j, a.z i (j, false) = false) :
    decode (encode a k) = ⟨n, a, k⟩ := by
  apply instance_ext (decode (encode a k)) ⟨n, a, k⟩ (show (decode (encode a k)).qubits = n from List.length_ofFn) rfl
  · intro i p
    rcases p with ⟨j, b⟩
    have hi : i.val < n := by simpa [decode, encode] using i.isLt
    have hj : j.val < n := by simpa [decode, encode] using j.isLt
    cases b <;> simp [decode, encode, readBit, hi, hj, hx]
    rfl
  · intro i p
    rcases p with ⟨j, b⟩
    have hi : i.val < n := by simpa [decode, encode] using i.isLt
    have hj : j.val < n := by simpa [decode, encode] using j.isLt
    cases b <;> simp [decode, encode, readBit, hi, hj, hz]
    rfl

theorem compile_encode {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (k : Nat) :
    compile.eval ((encodeRow t, List.ofFn (fun a => encodeRow (X a))), k) =
      encode (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k := by
  rw [compile_eval, rowA_correct, rowB_correct]
  simp only [wireList_eq]
  rfl

theorem compile_correct {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) (k : Nat) :
    Accepts (compile.eval ((encodeRow t, List.ofFn (fun a => encodeRow (X a))), k)) ↔
      Circuit.SynthesizesWithin (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k := by
  rw [compile_encode]
  unfold Accepts
  rw [decode_encode _ _ (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

end CliffordSynthesis.MatrixCompiler
