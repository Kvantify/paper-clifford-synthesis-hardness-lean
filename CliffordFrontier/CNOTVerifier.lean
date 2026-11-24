/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.Capped
public import CliffordComplexity.Program
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# CNOT Verifier

Polynomial-time verification and NP membership for CNOT-only synthesis.

A witness lists the CNOT indices in unary. The verifier checks the indices,
folds over the gates with two explicit Boolean matrix blocks as its state,
and compares the resulting tableau with the target tableau.
-/

@[expose] public section

namespace CliffordFrontier

open CliffordComplexity Turing.MultiTapeTM CliffordSynthesis CliffordSynthesis.MatrixCompiler

/-- A dense Boolean matrix represented by its row lists. -/
abbrev BitMatrix := List (List Bool)
/-- The pair of equal-width blocks used by a tableau simulator. -/
abbrev Blocks := BitMatrix × BitMatrix
/-- The control and target wire numbers of an encoded CNOT. -/
abbrev CNOTIndices := Nat × Nat

/-- Read a matrix entry, interpreting missing rows and columns as zero. -/
def entry (m : BitMatrix) (i j : Nat) : Bool :=
  (m.getD i []).getD j false

/-- Build a square Boolean matrix from its entries in row order. -/
def tabulate (n : Nat) (f : Nat → Nat → Bool) : BitMatrix :=
  (List.range n).map fun i => (List.range n).map (f i)

theorem entry_tabulate (n : Nat) (f : Nat → Nat → Bool) (i j : Fin n) :
    entry (tabulate n f) i.val j.val = f i.val j.val := by
  simp [entry, tabulate, List.getD_eq_getElem?_getD, i.isLt, j.isLt]

/-- Describe the Clifford tableau of the dense blocks, with zero extension. -/
private def asTableau (n : Nat) (b : Blocks) : Circuit.Tableau n where
  x i p := if p.2 then false else entry b.1 i.val p.1.val
  z i p := if p.2 then entry b.2 i.val p.1.val else false

/-- Apply a CNOT to two explicit blocks. The dimension comes from the row list. -/
def applyCNOTBlocks (x : Blocks × CNOTIndices) : Blocks :=
  let n := x.1.1.length
  let (c, t) := x.2
  (tabulate n fun i j => if i = t then entry x.1.1 i j ^^ entry x.1.1 c j else entry x.1.1 i j,
    tabulate n fun i j => if i = c then entry x.1.2 i j ^^ entry x.1.2 t j else entry x.1.2 i j)

private theorem applyCNOTBlocks_correct (b : Blocks) (c t : Fin b.1.length) :
    Circuit.Same (asTableau b.1.length (applyCNOTBlocks (b, c.val, t.val)))
      (Circuit.cnot c t (asTableau b.1.length b)) := by
  intro i p
  obtain ⟨j, p⟩ := p
  cases p <;> simp [applyCNOTBlocks, asTableau, Circuit.cnot, entry_tabulate, ← Fin.val_inj]

/-- The pair of identity matrices for the CNOT simulator’s starting tableau. -/
def identityBlocks (n : Nat) : Blocks :=
  let block := tabulate n fun i j => decide (i = j)
  (block, block)

private theorem same_eq {n : Nat} {a b : Circuit.Tableau n} (h : Circuit.Same a b) : a = b := by
  cases a
  cases b
  congr
  · exact funext fun i => funext fun p => (h i p).1
  · exact funext fun i => funext fun p => (h i p).2

private theorem asTableau_identity (n : Nat) : asTableau n (identityBlocks n) = Circuit.identity n := by
  apply same_eq
  intro i p
  rcases p with ⟨j, b⟩
  cases b <;> simp [asTableau, identityBlocks, Circuit.identity, entry_tabulate, ← Fin.val_inj]

private theorem applyCNOTBlocks_length (x : Blocks × CNOTIndices) :
    (applyCNOTBlocks x).1.length = x.1.1.length := by
  simp [applyCNOTBlocks, tabulate]

private def gateIndices {n : Nat} (g : RowExtraction.AddGate n) : CNOTIndices :=
  (g.control.val, g.target.val)

private theorem runBlocks_correct {n : Nat} (gs : List (RowExtraction.AddGate n)) (b : Blocks)
    (hb : b.1.length = n) :
    asTableau n ((gs.map gateIndices).foldl (fun state g => applyCNOTBlocks (state, g)) b) =
      Circuit.run (RowHistory.asCircuit gs) (asTableau n b) := by
  induction gs generalizing b with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, RowHistory.asCircuit, Circuit.run]
    rw [ih _ ((applyCNOTBlocks_length (b, gateIndices g)).trans hb)]
    congr 1
    subst n
    exact same_eq (applyCNOTBlocks_correct b g.control g.target)

/-- Check that the control and target are distinct wires within range. -/
def validIndices (n : Nat) (g : CNOTIndices) : Bool :=
  decide (g.1 < n ∧ g.2 < n ∧ g.1 ≠ g.2)

private theorem indices_are_valid {n : Nat} (g : RowExtraction.AddGate n) :
    validIndices n (gateIndices g) = true := by
  exact decide_eq_true ⟨g.control.isLt, g.target.isLt, fun h => g.distinct (Fin.val_inj.mp h)⟩

private theorem exists_typed_gates {n : Nat} (raw : List CNOTIndices)
    (h : raw.all (validIndices n) = true) :
    ∃ gs : List (RowExtraction.AddGate n), gs.map gateIndices = raw := by
  induction raw with
  | nil => exact ⟨[], rfl⟩
  | cons g tail ih =>
    simp only [List.all_cons, Bool.and_eq_true, validIndices, decide_eq_true_eq] at h
    obtain ⟨gs, rfl⟩ := ih h.2
    obtain ⟨hc, ht, hne⟩ := h.1
    exact ⟨⟨⟨g.1, hc⟩, ⟨g.2, ht⟩, fun he => hne (congrArg Fin.val he)⟩ :: gs, rfl⟩

/-- Compare two block pairs entrywise up to the supplied width. -/
def compareBlocks (n : Nat) (a b : Blocks) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    decide (entry a.1 i j = entry b.1 i j) && decide (entry a.2 i j = entry b.2 i j)

private theorem compareBlocks_iff (n : Nat) (a b : Blocks) :
    compareBlocks n a b = true ↔ Circuit.Same (asTableau n a) (asTableau n b) := by
  simp only [compareBlocks, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h i p
    obtain ⟨j, p⟩ := p
    have hentries := h i.val i.isLt j.val j.isLt
    cases p <;> simp [asTableau, hentries]
  · intro h i hi j hj
    have hx := (h ⟨i, hi⟩ (⟨j, hj⟩, false)).1
    have hz := (h ⟨i, hi⟩ (⟨j, hj⟩, true)).2
    exact ⟨hx, hz⟩

/-- Check the CNOT count, wire indices, and simulated output against the target. -/
def verifyRawCNOT (x : OutputTy.denote × List CNOTIndices) : Bool :=
  let out := x.1
  let n := out.1.length
  let k := out.2.2
  let expected := (out.1, out.2.1)
  let emitted := x.2.foldl (fun state g => applyCNOTBlocks (state, g)) (identityBlocks n)
  decide (x.2.length ≤ k) && x.2.all (validIndices n) && compareBlocks n emitted expected

private theorem decode_asTableau (out : OutputTy.denote) :
    (decode out).tableau = asTableau out.1.length (out.1, out.2.1) := by
  simp [decode, asTableau, entry, readBit, List.getD_eq_getElem?_getD]

private theorem verifyRawCNOT_encoding_iff (out : OutputTy.denote)
    (gs : List (RowExtraction.AddGate (decode out).qubits)) :
    verifyRawCNOT (out, gs.map gateIndices) = true ↔
      gs.length ≤ (decode out).threshold ∧
      Circuit.Same (Circuit.run (RowHistory.asCircuit gs) (Circuit.identity (decode out).qubits))
        (decode out).tableau := by
  have hvalid : (gs.map gateIndices).all (validIndices out.1.length) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    exact indices_are_valid g
  have hlen : (identityBlocks out.1.length).1.length = (decode out).qubits := by
    simp [identityBlocks, tabulate, decode]
  simp only [verifyRawCNOT, Bool.and_eq_true, hvalid, and_true, decide_eq_true_eq, List.length_map]
  rw [compareBlocks_iff]
  have hinit : asTableau (decode out).qubits (identityBlocks out.1.length) =
      Circuit.identity (decode out).qubits := asTableau_identity _
  have heval := runBlocks_correct gs _ hlen
  rw [hinit] at heval
  exact and_congr_right fun _ =>
    Iff.of_eq (congrArg₂ Circuit.Same heval (decode_asTableau out).symm)

theorem verifyRawCNOT_sound (out : OutputTy.denote) (raw : List CNOTIndices)
    (h : verifyRawCNOT (out, raw) = true) :
    CNOTOnly out := by
  have hvalid : raw.all (validIndices (decode out).qubits) = true := by
    simp only [verifyRawCNOT, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨gs, rfl⟩ := exists_typed_gates raw hvalid
  obtain ⟨hc, hs⟩ := (verifyRawCNOT_encoding_iff out gs).mp h
  exact ⟨gs, hc, hs⟩

/-- The framed list-of-lists encoding of an explicit Boolean matrix. -/
abbrev encMatrix : BitMatrix ↪ List Bool := encList (encList encBool)
/-- Encode two matrices in a framed pair. -/
abbrev encBlocks : Blocks ↪ List Bool := encPair encMatrix encMatrix
/-- Encode the control and target wire indices in unary. -/
abbrev encCNOTIndices : CNOTIndices ↪ List Bool := encPair encUnary encUnary

theorem entry_polyTime {α : Type} {enc : α ↪ List Bool} {m : α → BitMatrix}
    {i j : α → Nat} (hm : ComputableInPolyTime m enc encMatrix)
    (hi : ComputableInPolyTime i enc encUnary) (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun a => entry (m a) (i a) (j a)) enc encBool :=
  ComputableInPolyTime.listGetDWithInput
    (ComputableInPolyTime.listGetDWithInput hm hi []) hj false

theorem tabulate_polyTime {α : Type} {enc : α ↪ List Bool} {n : α → Nat}
    {f : α → Nat → Nat → Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hf : ComputableInPolyTime (fun q : (α × Nat) × Nat => f q.1.1 q.1.2 q.2)
      (encPair (encPair enc encUnary) encUnary) encBool) :
    ComputableInPolyTime (fun x => tabulate (n x) (f x)) enc encMatrix := by
  have rows := ComputableInPolyTime.unary_range' hn
  have cols := rows.comp (ComputableInPolyTime.fst enc encUnary)
  exact ComputableInPolyTime.mapWithInput rows (ComputableInPolyTime.mapWithInput cols hf)

private theorem cnotMatrix_polyTime {α : Type} {enc : α ↪ List Bool}
    {n source target : α → Nat} {m : α → BitMatrix}
    (hn : ComputableInPolyTime n enc encUnary)
    (hsource : ComputableInPolyTime source enc encUnary)
    (htarget : ComputableInPolyTime target enc encUnary)
    (hm : ComputableInPolyTime m enc encMatrix) :
    ComputableInPolyTime (fun x => tabulate (n x) fun i j =>
      if i = target x then entry (m x) i j ^^ entry (m x) (source x) j else entry (m x) i j)
      enc encMatrix := by
  apply tabulate_polyTime hn
  have outer := ComputableInPolyTime.fst (encPair enc encUnary) encUnary
  have col := ComputableInPolyTime.snd (encPair enc encUnary) encUnary
  have matrix := hm.comp outer.fst'
  have entryAt := entry_polyTime matrix outer.snd' col
  have sourceEntry := entry_polyTime matrix (hsource.comp outer.fst') col
  have isTarget := outer.snd'.decide_eq' (htarget.comp outer.fst')
  have xored := ComputableInPolyTime.bool_xor.comp (entryAt.prod sourceEntry)
  simpa only [Function.comp_apply, decide_eq_true_eq] using isTarget.ite xored entryAt

theorem applyCNOTBlocks_polyTime :
    ComputableInPolyTime applyCNOTBlocks (encPair encBlocks encCNOTIndices) encBlocks := by
  have blocks := ComputableInPolyTime.fst encBlocks encCNOTIndices
  have indices := ComputableInPolyTime.snd encBlocks encCNOTIndices
  have width := (ComputableInPolyTime.length_list (encList encBool)).comp blocks.fst'
  have x := cnotMatrix_polyTime width indices.fst' indices.snd' blocks.fst'
  have z := cnotMatrix_polyTime width indices.snd' indices.fst' blocks.snd'
  exact (x.prod z).of_enc_eq (by
    rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩
    rfl)

theorem identityBlocks_polyTime : ComputableInPolyTime identityBlocks encUnary encBlocks := by
  have outer := ComputableInPolyTime.fst (encPair encUnary encUnary) encUnary
  have col := ComputableInPolyTime.snd (encPair encUnary encUnary) encUnary
  have block := tabulate_polyTime (f := fun (_ : Nat) i j => decide (i = j))
    ComputableInPolyTime.id' (outer.snd'.decide_eq' col)
  exact block.prod block

private theorem allEntries_polyTime {α : Type} {enc : α ↪ List Bool} {n : α → Nat}
    {f : α → Nat → Nat → Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hf : ComputableInPolyTime (fun q : (α × Nat) × Nat => f q.1.1 q.1.2 q.2)
      (encPair (encPair enc encUnary) encUnary) encBool) :
    ComputableInPolyTime (fun x => (List.range (n x)).all fun i =>
      (List.range (n x)).all (f x i)) enc encBool := by
  have rows := ComputableInPolyTime.unary_range' hn
  have cols := rows.comp (ComputableInPolyTime.fst enc encUnary)
  exact ComputableInPolyTime.allWithInput rows (ComputableInPolyTime.allWithInput cols hf)

theorem compareBlocks_polyTime :
    ComputableInPolyTime (fun x : Nat × Blocks × Blocks => compareBlocks x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encBlocks encBlocks)) encBool := by
  unfold compareBlocks
  let encInput := encPair encUnary (encPair encBlocks encBlocks)
  apply allEntries_polyTime (ComputableInPolyTime.fst encUnary (encPair encBlocks encBlocks))
  have outer := ComputableInPolyTime.fst (encPair encInput encUnary) encUnary
  have col := ComputableInPolyTime.snd (encPair encInput encUnary) encUnary
  have row := outer.snd'
  have blocks := outer.fst'.snd'
  have firstMatrix := (entry_polyTime blocks.fst'.fst' row col).decide_eq'
    (entry_polyTime blocks.snd'.fst' row col)
  have secondMatrix := (entry_polyTime blocks.fst'.snd' row col).decide_eq'
    (entry_polyTime blocks.snd'.snd' row col)
  exact ComputableInPolyTime.bool_and.comp (firstMatrix.prod secondMatrix)

theorem validIndices_polyTime :
    ComputableInPolyTime (fun x : Nat × CNOTIndices => validIndices x.1 x.2)
      (encPair encUnary encCNOTIndices) encBool := by
  have width := ComputableTidilyInPolyTime.fst encUnary encCNOTIndices
  have gate := ComputableTidilyInPolyTime.snd encUnary encCNOTIndices
  have control := gate.fst'
  have target := gate.snd'
  have bounds := (ComputableTidilyInPolyTime.unary_lt' control width).bool_and'
    (ComputableTidilyInPolyTime.unary_lt' target width)
  have distinct := ComputableTidilyInPolyTime.bool_not.comp (control.decide_eq' target)
  refine (bounds.bool_and' distinct).computableInPolyTime.of_enc_eq fun p => ?_
  simp [validIndices, Function.comp_apply, Bool.decide_and, decide_not,
    Bool.and_assoc]

/-- Encode a list of CNOT instructions, with both indices in unary. -/
abbrev encRawCNOT : List (ℕ × ℕ) ↪ List Bool := encList encCNOTIndices

private noncomputable def cnotWitnessBound : Polynomial ℕ := 8 * (Polynomial.X + 1) ^ 3

private theorem rawCNOT_length_le (out : OutputTy.denote) (raw : List (ℕ × ℕ))
    (hcount : raw.length ≤ (out.1.length + 1) ^ 2)
    (hvalid : raw.all (fun g =>
      decide (g.1 < out.1.length ∧ g.2 < out.1.length ∧ g.1 ≠ g.2)) = true) :
    (encRawCNOT raw).length ≤ cnotWitnessBound.eval (encodeTy OutputTy out).length := by
  let n := out.1.length
  have hrow : n ≤ (encodeTy OutputTy out).length :=
    (length_le_length_encList (encList encBool) out.1).trans
      (length_le_encPair_left (encodeTy MatrixTy) (encodeTy (.pair MatrixTy .nat)) out)
  have hentry (g : ℕ × ℕ) (hg : g ∈ raw) : 2 * (encCNOTIndices g).length + 1 ≤ 6 * n + 3 := by
    have h := of_decide_eq_true (List.all_eq_true.mp hvalid g hg)
    have hc : g.1 < n := h.1
    have ht : g.2 < n := h.2.1
    simp only [show (encCNOTIndices g).length = _ from length_encPair g,
      encUnary_apply, List.length_replicate]
    omega
  have hraw : (encRawCNOT raw).length ≤ raw.length * (6 * n + 3) := by
    rw [length_encList]
    refine (List.sum_le_length_nsmul _ (6 * n + 3) ?_).trans ?_
    · intro k hk
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact hentry g hg
    · simp
  calc
    (encRawCNOT raw).length ≤ (n + 1) ^ 2 * (6 * n + 3) :=
      hraw.trans (Nat.mul_le_mul_right _ hcount)
    _ ≤ 8 * (n + 1) ^ 3 := by nlinarith
    _ ≤ cnotWitnessBound.eval (encodeTy OutputTy out).length := by
      simpa [cnotWitnessBound] using
        Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right hrow 1) 3)

/-- Encode a synthesis instance paired with its raw CNOT certificate. -/
abbrev encCNOTInput : OutputTy.denote × List CNOTIndices ↪ List Bool :=
  encPair (encodeTy OutputTy) encRawCNOT

/-- The matrix has exactly the specified number of rows and columns. -/
def Square (n : Nat) (b : BitMatrix) : Prop :=
  b.length = n ∧ ∀ row ∈ b, row.length = n

theorem tabulate_square (n : Nat) (f : Nat → Nat → Bool) : Square n (tabulate n f) := by
  constructor
  · simp [tabulate]
  · intro row hrow
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    simp

theorem square_encoded_size {n : Nat} {b : BitMatrix} (h : Square n b) :
    (encMatrix b).length ≤ n * (6 * n + 1) := by
  have hrows : ∀ row ∈ b, (encList encBool row).length ≤ 3 * n := by
    intro row hrow
    simpa [h.2 row hrow, Nat.mul_comm] using
      length_encList_le encBool row (b := 1) (by simp [encBool_apply])
  have hbound := length_encList_le (encList encBool) b hrows
  rw [h.1, show 2 * (3 * n) = 6 * n by omega] at hbound
  exact hbound

private theorem fold_square (n : Nat) (gs : List CNOTIndices) (b : Blocks)
    (ha : Square n b.1) (hb : Square n b.2) :
    let state := gs.foldl (fun state g => applyCNOTBlocks (state, g)) b
    Square n state.1 ∧ Square n state.2 := by
  induction gs generalizing b with
  | nil => exact ⟨ha, hb⟩
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (applyCNOTBlocks (b, g))
    · simpa only [applyCNOTBlocks, ha.1] using tabulate_square n _
    · simpa only [applyCNOTBlocks, ha.1] using tabulate_square n _

private theorem encCNOTInput_qubits_le (x : OutputTy.denote × List CNOTIndices) :
    x.1.1.length ≤ (encCNOTInput x).length :=
  ((length_le_length_encList (encList encBool) x.1.1).trans
    (length_le_encPair_left (encodeTy MatrixTy) (encodeTy (.pair MatrixTy .nat)) x.1)).trans
      (length_le_encPair_left (encodeTy OutputTy) encRawCNOT x)

private theorem fold_encoded_size (x : OutputTy.denote × List CNOTIndices) (i : Nat) :
    (encBlocks ((x.2.take i).foldl (fun state g => applyCNOTBlocks (state, g))
      (identityBlocks x.1.1.length))).length ≤ 22 * (x.1.1.length + 1) ^ 2 := by
  let n := x.1.1.length
  have hi : Square n (identityBlocks n).1 := tabulate_square n _
  obtain ⟨ha, hb⟩ := fold_square n (x.2.take i) (identityBlocks n) hi hi
  have h₁ := square_encoded_size ha
  have h₂ := square_encoded_size hb
  rw [length_encPair]
  nlinarith

theorem verifyRawCNOT_polyTime :
    ComputableInPolyTime verifyRawCNOT encCNOTInput encBool := by
  let eOut : OutputTy.denote ↪ List Bool := encPair encMatrix (encPair encMatrix encNat)
  have hOut := ComputableTidilyInPolyTime.fst eOut encRawCNOT
  have hW := ComputableTidilyInPolyTime.snd eOut encRawCNOT
  have hX := (ComputableTidilyInPolyTime.fst encMatrix (encPair encMatrix encNat)).comp hOut
  have hRest := (ComputableTidilyInPolyTime.snd encMatrix (encPair encMatrix encNat)).comp hOut
  have hZ := (ComputableTidilyInPolyTime.fst encMatrix encNat).comp hRest
  have hK := (ComputableTidilyInPolyTime.snd encMatrix encNat).comp hRest
  have hN := (ComputableTidilyInPolyTime.length_list (encList encBool)).comp hX
  have hWlen := (ComputableTidilyInPolyTime.length_list encCNOTIndices).comp hW
  have hRun := ComputableTidilyInPolyTime.foldl'
    (step := fun state g => applyCNOTBlocks (state, g))
    hW (identityBlocks_polyTime.tidy.comp hN) applyCNOTBlocks_polyTime.tidy
    (B := fun x => 22 * (x.1.1.length + 1) ^ 2)
    (.of_forall_le 22 2 fun x =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (encCNOTInput_qubits_le x) 1) 2))
    (fun x i _ => fold_encoded_size x i)
  have hCompare := compareBlocks_polyTime.tidy.comp (hN.prod (hRun.prod (hX.prod hZ)))
  have hBounds := ComputableTidilyInPolyTime.allWith validIndices_polyTime.tidy hN hW
  have hCount := ComputableTidilyInPolyTime.binary_le.comp
    ((ComputableTidilyInPolyTime.unary_to_binary.comp hWlen).prod hK)
  exact (hCount.bool_and' hBounds |>.bool_and' hCompare).computableInPolyTime

/-- Short CNOT witnesses give NP membership for a polynomial-time restriction of the language. -/
private theorem cnotOnly_mem_NP_of_short_circuits (A : Set OutputTy.denote)
    {guard : OutputTy.denote → Bool}
    (guardTime : ComputableInPolyTime guard (encodeTy OutputTy) encBool)
    (accepted : ∀ out, out ∈ A ↔ CNOTOnly out ∧ guard out = true)
    (short : ∀ out ∈ A, ∃ gs : List (RowExtraction.AddGate (decode out).qubits),
      gs.length ≤ (decode out).threshold ∧
      Circuit.Same (Circuit.run (RowHistory.asCircuit gs) (Circuit.identity (decode out).qubits))
        (decode out).tableau ∧ gs.length ≤ (out.1.length + 1) ^ 2) :
    A ∈ Cslib.Complexity.NP (encodeTy OutputTy) := by
  have verifierTime := ComputableInPolyTime.bool_and' verifyRawCNOT_polyTime
    (guardTime.comp (ComputableInPolyTime.fst (encodeTy OutputTy) encRawCNOT))
  apply Cslib.Complexity.mem_NP_of_check (p := cnotWitnessBound)
    (Decoder.list (Decoder.pair Decoder.unary Decoder.unary)) verifierTime
  · intro out raw h
    simp only [Bool.and_eq_true] at h
    exact (accepted out).mpr ⟨verifyRawCNOT_sound out raw h.1, h.2⟩
  · intro out hout
    obtain ⟨gs, hc, hs, hshort⟩ := short out hout
    refine ⟨gs.map gateIndices, ?_, ?_⟩
    · simp only [Bool.and_eq_true]
      exact ⟨(verifyRawCNOT_encoding_iff out gs).mpr ⟨hc, hs⟩, ((accepted out).mp hout).2⟩
    · apply rawCNOT_length_le
      · simpa using hshort
      · apply List.all_eq_true.mpr
        intro g hg
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
        exact indices_are_valid g

/-- The capped CNOT-only language has a polynomial-time verifier in Frontier. -/
theorem cappedCNOTOnly_mem_NP :
    {x | CappedCNOTOnly x} ∈ Cslib.Complexity.NP (encodeTy OutputTy) := by
  let guard := fun out : OutputTy.denote => decide (out.2.2 ≤ out.1.length)
  have guardTime : ComputableInPolyTime guard (encodeTy OutputTy) encBool := by
    let rest := encPair encMatrix encNat
    have threshold := (ComputableInPolyTime.snd encMatrix rest).snd'
    have width := (ComputableInPolyTime.length_list_binary (encList encBool)).comp
      (ComputableInPolyTime.fst encMatrix rest)
    exact ComputableInPolyTime.binary_le' threshold width
  refine cnotOnly_mem_NP_of_short_circuits _ guardTime (fun out => ?_) ?_
  · simp [CappedCNOTOnly, WithinQubits, decode, guard]
  · intro out hout
    obtain ⟨⟨gs, hc, hs⟩, hk⟩ := hout
    have hqubits : gs.length ≤ out.1.length := hc.trans hk
    exact ⟨gs, hc, hs, by nlinarith⟩

/-- A uniform quadratic synthesis bound gives NP membership for binary thresholds. -/
theorem cnotOnly_mem_NP_of_quadratic_bound
    (bound : ∀ out : OutputTy.denote, CNOTOnly out →
      HasCNOTCircuit {decode out with threshold := (decode out).qubits ^ 2}) :
    {x | CNOTOnly x} ∈ Cslib.Complexity.NP (encodeTy OutputTy) := by
  refine cnotOnly_mem_NP_of_short_circuits _ (ComputableInPolyTime.const true)
    (fun out => by simp) ?_
  intro out hout
  by_cases hk : (decode out).threshold ≤ (decode out).qubits ^ 2
  · obtain ⟨gs, hc, hs⟩ := hout
    have hshort : gs.length ≤ out.1.length ^ 2 := hc.trans hk
    exact ⟨gs, hc, hs, hshort.trans (Nat.pow_le_pow_left (Nat.le_succ _) 2)⟩
  · obtain ⟨gs, hc, hs⟩ := bound out hout
    have hcost : gs.length ≤ (decode out).threshold :=
      hc.trans (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    have hshort : gs.length ≤ out.1.length ^ 2 := hc
    exact ⟨gs, hcost, hs, hshort.trans (Nat.pow_le_pow_left (Nat.le_succ _) 2)⟩

end CliffordFrontier
