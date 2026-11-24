/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.CNOTVerifier
public import CliffordSynthesis.Certificates
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length

/-!
# Clifford Verifier

A polynomial-time verifier for CNOT-count minimization with free H and S.
Each state stores all four dense tableau blocks, including the off-diagonal blocks
that can occur during simulation of a circuit with single-qubit gates.
-/

public section

namespace CliffordFrontier

open CliffordComplexity Turing.MultiTapeTM CliffordSynthesis CliffordSynthesis.MatrixCompiler

/-- A full tableau, with the XX/ZX block pair followed by the XZ/ZZ block pair. -/
abbrev PackedTableau := Blocks × Blocks
/-- Two gate tag bits followed by the raw wire indices. -/
abbrev CliffordGateIndices := Bool × Bool × CNOTIndices

/-- Encode the two block pairs of the packed tableau. -/
abbrev encPackedTableau : PackedTableau ↪ List Bool := encPair encBlocks encBlocks
/-- Encode the gate tag bits followed by the unary wire indices. -/
abbrev encCliffordGateIndices : CliffordGateIndices ↪ List Bool :=
  encPair encBool (encPair encBool encCNOTIndices)

/-- Apply Hadamard or phase on one wire of a packed block pair. -/
@[expose] def applyLocalBlocks (x : Blocks × Bool × Nat) : Blocks :=
  let b := x.1
  let n := b.1.length
  let phase := x.2.1
  let q := x.2.2
  (tabulate n fun i j => if i = q then (if phase then entry b.1 i j else entry b.2 i j) else entry b.1 i j,
    tabulate n fun i j =>
      if i = q then (if phase then entry b.2 i j ^^ entry b.1 i j else entry b.1 i j)
      else entry b.2 i j)

/-- Apply a raw Hadamard, phase, or CNOT to the packed tableau. -/
@[expose] def applyCliffordBlocks (x : PackedTableau × CliffordGateIndices) : PackedTableau :=
  if x.2.1 then
    (applyCNOTBlocks (x.1.1, x.2.2.2), applyCNOTBlocks (x.1.2, x.2.2.2))
  else
    (applyLocalBlocks (x.1.1, x.2.2.1, x.2.2.2.1),
      applyLocalBlocks (x.1.2, x.2.2.1, x.2.2.2.1))

/-- A square matrix with every entry false. -/
@[expose] def zeroMatrix (n : Nat) : BitMatrix := tabulate n fun _ _ => false

/-- The packed full tableau of the identity Clifford operation. -/
@[expose] def identityPacked (n : Nat) : PackedTableau :=
  let I := identityBlocks n
  let O := zeroMatrix n
  ((I.1, O), (O, I.2))

/-- Compare both block pairs entrywise up to the specified width. -/
@[expose] def comparePacked (n : Nat) (a b : PackedTableau) : Bool :=
  compareBlocks n a.1 b.1 && compareBlocks n a.2 b.2

/-- Check the tag and wire indices for a supported Clifford instruction. -/
@[expose] def validCliffordIndices (n : Nat) (g : CliffordGateIndices) : Bool :=
  if g.1 then !g.2.1 && validIndices n g.2.2
  else decide (g.2.2.1 < n ∧ g.2.2.2 = 0)

/-- Translate an in-range Clifford gate to the verifier’s raw instruction. -/
@[expose] def encodeCliffordGate {n : Nat} : CliffordSynthesis.Circuit.Gate n → CliffordGateIndices
  | .H q => (false, false, q.val, 0)
  | .S q => (false, true, q.val, 0)
  | .CX c t _ => (true, false, c.val, t.val)

/-- Interpret the packed matrices as images of the Pauli generators. -/
@[expose] def asPackedTableau (n : Nat) (a : PackedTableau) : CliffordSynthesis.Circuit.Tableau n where
  x i p := entry (if p.2 then a.2.1 else a.1.1) i.val p.1.val
  z i p := entry (if p.2 then a.2.2 else a.1.2) i.val p.1.val

theorem identityPacked_correct (n : Nat) :
    asPackedTableau n (identityPacked n) = CliffordSynthesis.Circuit.identity n := by
  unfold asPackedTableau CliffordSynthesis.Circuit.identity
  congr 1
  all_goals
    funext i p
    rcases p with ⟨j, b⟩
    cases b <;> simp [identityPacked, identityBlocks, zeroMatrix, entry_tabulate, ← Fin.val_inj]

theorem applyCliffordBlocks_correct {n : Nat} (a : PackedTableau)
    (hx : a.1.1.length = n) (hz : a.2.1.length = n)
    (g : CliffordSynthesis.Circuit.Gate n) :
    CliffordSynthesis.Circuit.Same (asPackedTableau n (applyCliffordBlocks (a, encodeCliffordGate g)))
      (CliffordSynthesis.Circuit.applyGate g (asPackedTableau n a)) := by
  intro i p
  obtain ⟨j, b⟩ := p
  cases g <;> cases b <;>
    simp [applyCliffordBlocks, applyCNOTBlocks, applyLocalBlocks, asPackedTableau, encodeCliffordGate,
      CliffordSynthesis.Circuit.applyGate, CliffordSynthesis.Circuit.hadamard,
      CliffordSynthesis.Circuit.phase, CliffordSynthesis.Circuit.cnot, hx, hz,
      entry_tabulate, ← Fin.val_inj]
  all_goals
    constructor <;> split <;> simp_all

theorem applyCliffordBlocks_rows (x : PackedTableau × CliffordGateIndices) :
    (applyCliffordBlocks x).1.1.length = x.1.1.1.length ∧
      (applyCliffordBlocks x).2.1.length = x.1.2.1.length := by
  rcases x with ⟨⟨_, _⟩, ⟨_, _, _, _⟩⟩
  simp [applyCliffordBlocks, applyCNOTBlocks, applyLocalBlocks, tabulate, apply_ite]

theorem encodeCliffordGate_valid {n : Nat} (g : CliffordSynthesis.Circuit.Gate n) :
    validCliffordIndices n (encodeCliffordGate g) = true := by
  cases g with
  | H q => simp [validCliffordIndices, encodeCliffordGate, q.isLt]
  | S q => simp [validCliffordIndices, encodeCliffordGate, q.isLt]
  | CX c t h =>
    have hne : c.val ≠ t.val := fun he => h (Fin.ext he)
    simp [validCliffordIndices, encodeCliffordGate, validIndices, c.isLt, t.isLt, hne]

theorem exists_encodedCliffordGate {n : Nat} (raw : CliffordGateIndices)
    (h : validCliffordIndices n raw = true) :
    ∃ g : CliffordSynthesis.Circuit.Gate n, encodeCliffordGate g = raw := by
  rcases raw with ⟨paid, s, c, t⟩
  cases paid
  · simp [validCliffordIndices] at h
    obtain ⟨hc, rfl⟩ := h
    cases s
    · exact ⟨.H ⟨c, hc⟩, rfl⟩
    · exact ⟨.S ⟨c, hc⟩, rfl⟩
  · simp [validCliffordIndices, validIndices] at h
    obtain ⟨rfl, hc, ht, hct⟩ := h
    exact ⟨.CX ⟨c, hc⟩ ⟨t, ht⟩ (fun e => hct (congrArg Fin.val e)), rfl⟩

theorem applyLocalBlocks_polyTime :
    ComputableInPolyTime applyLocalBlocks (encPair encBlocks (encPair encBool encUnary)) encBlocks := by
  let encInput := encPair encBlocks (encPair encBool encUnary)
  let encOuter := encPair encInput encUnary
  have data := ComputableInPolyTime.fst encBlocks (encPair encBool encUnary)
  have width := (ComputableInPolyTime.length_list (encList encBool)).comp data.fst'
  have outer := ComputableInPolyTime.fst encOuter encUnary
  have col := ComputableInPolyTime.snd encOuter encUnary
  have input := outer.fst'
  have row := outer.snd'
  have x := entry_polyTime (data.fst'.comp input) row col
  have z := entry_polyTime (data.snd'.comp input) row col
  have settings := ComputableInPolyTime.snd encBlocks (encPair encBool encUnary)
  have phase := settings.fst'.comp input
  have isTarget := row.decide_eq' (settings.snd'.comp input)
  have zXorX := ComputableInPolyTime.bool_xor.comp (z.prod x)
  have updateX := isTarget.ite (phase.ite x z) x
  have updateZ := isTarget.ite (phase.ite zXorX x) z
  have updateXMatrix := tabulate_polyTime (f := fun x i j =>
    if i = x.2.2 then (if x.2.1 then entry x.1.1 i j else entry x.1.2 i j)
    else entry x.1.1 i j) width (by
      simpa only [Function.comp_apply, decide_eq_true_eq] using updateX)
  have updateZMatrix := tabulate_polyTime (f := fun x i j =>
    if i = x.2.2 then (if x.2.1 then entry x.1.2 i j ^^ entry x.1.1 i j else entry x.1.1 i j)
    else entry x.1.2 i j) width (by
      simpa only [Function.comp_apply, decide_eq_true_eq] using updateZ)
  exact updateXMatrix.prod updateZMatrix

theorem applyCliffordBlocks_polyTime :
    ComputableInPolyTime applyCliffordBlocks
      (encPair encPackedTableau encCliffordGateIndices) encPackedTableau := by
  have blocks := ComputableInPolyTime.fst encPackedTableau encCliffordGateIndices
  have gate := ComputableInPolyTime.snd encPackedTableau encCliffordGateIndices
  have phase := gate.snd'.fst'
  have indices := gate.snd'.snd'
  have leftCNOT := applyCNOTBlocks_polyTime.comp (blocks.fst'.prod indices)
  have rightCNOT := applyCNOTBlocks_polyTime.comp (blocks.snd'.prod indices)
  have localGate := phase.prod indices.fst'
  have leftLocal := applyLocalBlocks_polyTime.comp (blocks.fst'.prod localGate)
  have rightLocal := applyLocalBlocks_polyTime.comp (blocks.snd'.prod localGate)
  exact gate.fst'.ite (leftCNOT.prod rightCNOT) (leftLocal.prod rightLocal)

theorem identityPacked_polyTime :
    ComputableInPolyTime identityPacked encUnary encPackedTableau := by
  have zero := tabulate_polyTime (f := fun _ _ _ => false) (enc := encUnary)
    ComputableInPolyTime.id' (ComputableInPolyTime.const false)
  exact (identityBlocks_polyTime.fst'.prod zero).prod (zero.prod identityBlocks_polyTime.snd')

theorem comparePacked_polyTime :
    ComputableInPolyTime (fun x : Nat × PackedTableau × PackedTableau => comparePacked x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encPackedTableau encPackedTableau)) encBool := by
  have width := ComputableInPolyTime.fst encUnary (encPair encPackedTableau encPackedTableau)
  have states := ComputableInPolyTime.snd encUnary (encPair encPackedTableau encPackedTableau)
  have left := compareBlocks_polyTime.comp (width.prod (states.fst'.fst'.prod states.snd'.fst'))
  have right := compareBlocks_polyTime.comp (width.prod (states.fst'.snd'.prod states.snd'.snd'))
  exact ComputableInPolyTime.bool_and.comp (left.prod right)

theorem validCliffordIndices_polyTime :
    ComputableInPolyTime (fun x : Nat × CliffordGateIndices => validCliffordIndices x.1 x.2)
      (encPair encUnary encCliffordGateIndices) encBool := by
  have width := ComputableInPolyTime.fst encUnary encCliffordGateIndices
  have gate := ComputableInPolyTime.snd encUnary encCliffordGateIndices
  have phase := gate.snd'.fst'
  have indices := gate.snd'.snd'
  have validCNOT := validIndices_polyTime.comp (width.prod indices)
  have hnot := ComputableInPolyTime.bool_not.comp phase
  have hlt := ComputableTidilyInPolyTime.unary_lt' indices.fst'.tidy width.tidy
  have hzero := indices.snd'.decide_eq' (ComputableInPolyTime.const 0)
  have hlocal := ComputableInPolyTime.bool_and.comp (hlt.computableInPolyTime.prod hzero)
  refine (gate.fst'.ite (ComputableInPolyTime.bool_and.comp (hnot.prod validCNOT)) hlocal).of_enc_eq
    fun p => ?_
  simp [validCliffordIndices, Function.comp_apply, Bool.decide_and]

private theorem packedTableau_eq {n : Nat} {a b : Circuit.Tableau n}
    (h : Circuit.Same a b) : a = b := by
  cases a
  cases b
  congr
  · exact funext fun i => funext fun p => (h i p).1
  · exact funext fun i => funext fun p => (h i p).2

private theorem identityPacked_rows (n : Nat) :
    (identityPacked n).1.1.length = n ∧ (identityPacked n).2.1.length = n := by
  simp [identityPacked, identityBlocks, zeroMatrix, tabulate]

private theorem runCliffordBlocks_correct {n : Nat} (gs : List (Circuit.Gate n))
    (a : PackedTableau) (hx : a.1.1.length = n) (hz : a.2.1.length = n) :
    asPackedTableau n ((gs.map encodeCliffordGate).foldl
      (fun state gate => applyCliffordBlocks (state, gate)) a) =
    Circuit.run gs (asPackedTableau n a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, Circuit.run]
    have hrows := applyCliffordBlocks_rows (a, encodeCliffordGate g)
    rw [ih _ (hrows.1.trans hx) (hrows.2.trans hz)]
    rw [packedTableau_eq (applyCliffordBlocks_correct a hx hz g)]

private theorem rawCliffordGates_decode {n : Nat} (raw : List CliffordGateIndices)
    (h : raw.all (validCliffordIndices n) = true) :
    ∃ gs : List (Circuit.Gate n), gs.map encodeCliffordGate = raw := by
  induction raw with
  | nil => exact ⟨[], rfl⟩
  | cons g raw ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨g', rfl⟩ := exists_encodedCliffordGate g h.1
    obtain ⟨gs, rfl⟩ := ih h.2
    exact ⟨g' :: gs, rfl⟩

private theorem rawCliffordGates_countP {n : Nat} (gs : List (Circuit.Gate n)) :
    (gs.map encodeCliffordGate).countP Prod.fst = Circuit.cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [Circuit.cost, Circuit.paid, encodeCliffordGate, ih,
      Nat.add_comm]

private theorem comparePacked_iff (n : Nat) (a b : PackedTableau) :
    comparePacked n a b = true ↔ Circuit.Same (asPackedTableau n a) (asPackedTableau n b) := by
  simp only [comparePacked, compareBlocks, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  constructor
  · intro h i p
    obtain ⟨j, flag⟩ := p
    cases flag
    · exact h.1 i.val i.isLt j.val j.isLt
    · exact h.2 i.val i.isLt j.val j.isLt
  · intro h
    constructor <;> intro i hi j hj
    · exact h ⟨i, hi⟩ (⟨j, hj⟩, false)
    · exact h ⟨i, hi⟩ (⟨j, hj⟩, true)

private def targetPacked (out : OutputTy.denote) : PackedTableau :=
  let zero := zeroMatrix out.1.length
  ((out.1, zero), (zero, out.2.1))

private theorem targetPacked_correct (out : OutputTy.denote) :
    asPackedTableau out.1.length (targetPacked out) = (decode out).tableau := by
  unfold asPackedTableau targetPacked decode
  congr 1
  all_goals
    funext i p
    rcases p with ⟨j, flag⟩
    cases flag <;>
      first
      | exact entry_tabulate _ (fun _ _ => false) i j
      | simp [entry, readBit, List.getD_eq_getElem?_getD]

/-- Test a circuit with explicit unary wire indices against a binary-threshold synthesis instance. -/
def verifyRawClifford (x : OutputTy.denote × List CliffordGateIndices) : Bool :=
  let out := x.1
  let n := out.1.length
  let result := x.2.foldl (fun state gate => applyCliffordBlocks (state, gate)) (identityPacked n)
  decide (x.2.countP Prod.fst ≤ out.2.2) &&
    x.2.all (validCliffordIndices n) && comparePacked n result (targetPacked out)

private theorem verifyRawClifford_encoding_iff (out : OutputTy.denote)
    (gs : List (Circuit.Gate (decode out).qubits)) :
    verifyRawClifford (out, gs.map encodeCliffordGate) = true ↔
      Circuit.cost gs ≤ (decode out).threshold ∧
        Circuit.Same (Circuit.run gs (Circuit.identity (decode out).qubits)) (decode out).tableau := by
  have hvalid : (gs.map encodeCliffordGate).all (validCliffordIndices out.1.length) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    exact encodeCliffordGate_valid g
  simp only [verifyRawClifford, Bool.and_eq_true, rawCliffordGates_countP, hvalid,
    and_true, decide_eq_true_eq, comparePacked_iff]
  have hrows : (identityPacked out.1.length).1.1.length = (decode out).qubits ∧
      (identityPacked out.1.length).2.1.length = (decode out).qubits :=
    identityPacked_rows _
  have hinit : asPackedTableau (decode out).qubits (identityPacked out.1.length) =
      Circuit.identity (decode out).qubits := identityPacked_correct _
  have heval := runCliffordBlocks_correct gs _ hrows.1 hrows.2
  rw [hinit] at heval
  exact and_congr_right fun _ => Iff.of_eq
    (congrArg₂ Circuit.Same heval (targetPacked_correct out))

theorem verifyRawClifford_sound (out : OutputTy.denote) (raw : List CliffordGateIndices)
    (h : verifyRawClifford (out, raw) = true) : Accepts out := by
  have hvalid : raw.all (validCliffordIndices (decode out).qubits) = true := by
    simp only [verifyRawClifford, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨gs, rfl⟩ := rawCliffordGates_decode raw hvalid
  obtain ⟨hc, hs⟩ := (verifyRawClifford_encoding_iff out gs).mp h
  exact ⟨gs, hc, hs⟩

private def PackedSquare (n : Nat) (a : PackedTableau) : Prop :=
  Square n a.1.1 ∧ Square n a.1.2 ∧ Square n a.2.1 ∧ Square n a.2.2

private theorem identityPacked_square (n : Nat) : PackedSquare n (identityPacked n) := by
  simp [PackedSquare, identityPacked, identityBlocks, zeroMatrix, tabulate_square]

private theorem applyCliffordBlocks_square (n : Nat) (x : PackedTableau × CliffordGateIndices)
    (hx : x.1.1.1.length = n) (hz : x.1.2.1.length = n) :
    PackedSquare n (applyCliffordBlocks x) := by
  rcases x with ⟨a, paid, s, c, t⟩
  cases paid <;>
    simp [PackedSquare, applyCliffordBlocks, applyCNOTBlocks, applyLocalBlocks, hx, hz,
      tabulate_square]

private theorem packed_fold_square (n : Nat) (gs : List CliffordGateIndices) (a : PackedTableau)
    (h : PackedSquare n a) :
    PackedSquare n (gs.foldl (fun state g => applyCliffordBlocks (state, g)) a) := by
  induction gs generalizing a with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ (applyCliffordBlocks_square n (a, g) h.1.1 h.2.2.1.1)

private abbrev encRawClifford : List CliffordGateIndices ↪ List Bool := encList encCliffordGateIndices
private abbrev encCliffordInput : OutputTy.denote × List CliffordGateIndices ↪ List Bool :=
  encPair (encodeTy OutputTy) encRawClifford

private theorem out_qubits_le (out : OutputTy.denote) :
    out.1.length ≤ (encodeTy OutputTy out).length :=
  (length_le_length_encList (encList encBool) out.1).trans
    (length_le_encPair_left (encodeTy MatrixTy) (encodeTy (.pair MatrixTy .nat)) out)

private theorem encCliffordInput_qubits_le (x : OutputTy.denote × List CliffordGateIndices) :
    x.1.1.length ≤ (encCliffordInput x).length :=
  (out_qubits_le x.1).trans (length_le_encPair_left (encodeTy OutputTy) encRawClifford x)

private theorem packed_fold_encoded_size (x : OutputTy.denote × List CliffordGateIndices) (i : Nat) :
    (encPackedTableau ((x.2.take i).foldl (fun state g => applyCliffordBlocks (state, g))
      (identityPacked x.1.1.length))).length ≤ 64 * (x.1.1.length + 1) ^ 2 := by
  let n := x.1.1.length
  obtain ⟨hxx, hzx, hxz, hzz⟩ := packed_fold_square n (x.2.take i) (identityPacked n)
    (identityPacked_square n)
  have h₁ := square_encoded_size hxx
  have h₂ := square_encoded_size hzx
  have h₃ := square_encoded_size hxz
  have h₄ := square_encoded_size hzz
  simp only [encPackedTableau, encBlocks, length_encPair]
  nlinarith

private theorem verifyRawClifford_polyTime :
    ComputableInPolyTime verifyRawClifford encCliffordInput encBool := by
  let eOut : OutputTy.denote ↪ List Bool := encPair encMatrix (encPair encMatrix encNat)
  have out := ComputableTidilyInPolyTime.fst eOut encRawClifford
  have witness := ComputableTidilyInPolyTime.snd eOut encRawClifford
  have width := (ComputableTidilyInPolyTime.length_list (encList encBool)).comp out.fst'
  have threshold := out.snd'.snd'
  have run := ComputableTidilyInPolyTime.foldl'
    (step := fun state g => applyCliffordBlocks (state, g))
    witness (identityPacked_polyTime.tidy.comp width) applyCliffordBlocks_polyTime.tidy
    (B := fun x => 64 * (x.1.1.length + 1) ^ 2)
    (.of_forall_le 64 2 fun x =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right (encCliffordInput_qubits_le x) 1) 2))
    (fun x i _ => packed_fold_encoded_size x i)
  have zero := (tabulate_polyTime (f := fun _ _ _ => false) (enc := encUnary)
    ComputableInPolyTime.id' (ComputableInPolyTime.const false)).tidy.comp width
  have target := (out.fst'.prod zero).prod (zero.prod out.snd'.fst')
  have compare := comparePacked_polyTime.tidy.comp (width.prod (run.prod target))
  have valid := ComputableTidilyInPolyTime.allWith validCliffordIndices_polyTime.tidy width witness
  -- The paid flag occupies the first bit of the gate tuple.
  have count := ComputableTidilyInPolyTime.countPWithInput (test := fun _ g => g.1) witness
    (ComputableTidilyInPolyTime.snd encCliffordInput encCliffordGateIndices).fst'
  have bound := ComputableTidilyInPolyTime.binary_le.comp
    ((ComputableTidilyInPolyTime.unary_to_binary.comp count).prod threshold)
  exact (bound.bool_and' valid |>.bool_and' compare).computableInPolyTime

private theorem rawClifford_length_le (n : Nat) (raw : List CliffordGateIndices)
    (hvalid : raw.all (validCliffordIndices n) = true) :
    (encRawClifford raw).length ≤ raw.length * (16 * (n + 1)) := by
  rw [length_encList]
  refine (List.sum_le_length_nsmul _ (16 * (n + 1)) ?_).trans ?_
  · intro k hk
    obtain ⟨⟨paid, phase, c, t⟩, hg, rfl⟩ := List.mem_map.mp hk
    have h := List.all_eq_true.mp hvalid _ hg
    have hbounds : c < n ∧ t ≤ n := by
      cases paid <;> simp [validCliffordIndices, validIndices] at h <;> omega
    simp only [encCliffordGateIndices, encCNOTIndices, length_encPair, encBool_apply,
      List.length_singleton, encUnary_apply, List.length_replicate]
    omega
  · simp

/-- A polynomial bound on circuit length makes the guarded acceptance language an NP language. -/
theorem clifford_mem_NP_of_short_circuits (A : Set OutputTy.denote)
    {guard : OutputTy.denote → Bool}
    (guardTime : ComputableInPolyTime guard (encodeTy OutputTy) encBool)
    (accepts_iff : ∀ out, out ∈ A ↔ Accepts out ∧ guard out = true)
    (bound : Polynomial Nat)
    (short : ∀ out ∈ A, ∃ gs : List (Circuit.Gate (decode out).qubits),
      Circuit.cost gs ≤ (decode out).threshold ∧
        Circuit.Same (Circuit.run gs (Circuit.identity (decode out).qubits)) (decode out).tableau ∧
        gs.length ≤ bound.eval (encodeTy OutputTy out).length) :
    A ∈ Cslib.Complexity.NP (encodeTy OutputTy) := by
  let decoder := Decoder.list (Decoder.pair Decoder.bool (Decoder.pair Decoder.bool
    (Decoder.pair Decoder.unary Decoder.unary)))
  let verifier := fun x : OutputTy.denote × List CliffordGateIndices =>
    verifyRawClifford x && guard x.1
  have verifierTime : ComputableInPolyTime verifier encCliffordInput encBool :=
    ComputableInPolyTime.bool_and' verifyRawClifford_polyTime
      (guardTime.comp (ComputableInPolyTime.fst (encodeTy OutputTy) encRawClifford))
  apply Cslib.Complexity.mem_NP_of_check (p := bound * (16 * (Polynomial.X + 1))) decoder verifierTime
  · intro out raw h
    have hchecks : verifyRawClifford (out, raw) = true ∧ guard out = true := by
      simpa only [verifier, Bool.and_eq_true] using h
    exact (accepts_iff out).mpr ⟨verifyRawClifford_sound out raw hchecks.1, hchecks.2⟩
  · intro out h
    obtain ⟨gs, hcost, hsame, hlen⟩ := short out h
    let raw := gs.map encodeCliffordGate
    refine ⟨raw, ?_, ?_⟩
    · simp only [verifier, Bool.and_eq_true]
      exact ⟨(verifyRawClifford_encoding_iff out gs).mpr ⟨hcost, hsame⟩, ((accepts_iff out).mp h).2⟩
    have hvalid : raw.all (validCliffordIndices out.1.length) = true := by
      apply List.all_eq_true.mpr
      intro g hg
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
      exact encodeCliffordGate_valid g
    have hsize := rawClifford_length_le out.1.length raw hvalid
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    exact hsize.trans (Nat.mul_le_mul (by simpa [raw] using hlen)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (out_qubits_le out) 1)))

/-- CNOT-count minimization with free local gates belongs to NP when the threshold is at most
the number of qubits. -/
theorem cappedClifford_mem_NP : {x | CappedClifford x} ∈
    Cslib.Complexity.NP (encodeTy OutputTy) := by
  let guard := fun out : OutputTy.denote => decide (out.2.2 ≤ out.1.length)
  have guardTime : ComputableInPolyTime guard (encodeTy OutputTy) encBool := by
    let rest := encPair encMatrix encNat
    have threshold := (ComputableInPolyTime.snd encMatrix rest).snd'
    have width := (ComputableInPolyTime.length_list_binary (encList encBool)).comp
      (ComputableInPolyTime.fst encMatrix rest)
    exact ComputableInPolyTime.binary_le' threshold width
  refine clifford_mem_NP_of_short_circuits _ guardTime (fun out => ?_)
    (4 * (Polynomial.X + 1) ^ 2) ?_
  · simp [guard, CappedClifford, WithinQubits, decode]
  · intro out hout
    obtain ⟨gs, hcost, hlen, hsame⟩ :=
      Certificates.bounded_certificate _ _ hout.1
    refine ⟨gs, hcost, hsame, hlen.trans ?_⟩
    have hk : (decode out).threshold ≤ (decode out).qubits := hout.2
    have hn : (decode out).qubits ≤ (encodeTy OutputTy out).length := out_qubits_le out
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    calc
      _ ≤ 3 * (decode out).qubits * ((decode out).qubits + 1) + (decode out).qubits := by
        gcongr
      _ ≤ 4 * ((decode out).qubits + 1) ^ 2 := by nlinarith
      _ ≤ _ := by gcongr

/-- A uniform quadratic synthesis bound suffices for NP membership with arbitrary binary thresholds. -/
theorem clifford_mem_NP_of_quadratic_synthesis
    (synthesisBound : ∀ out : OutputTy.denote, Accepts out →
      Circuit.SynthesizesWithin (decode out).tableau ((decode out).qubits ^ 2)) :
    {x | Accepts x} ∈ Cslib.Complexity.NP (encodeTy OutputTy) := by
  refine clifford_mem_NP_of_short_circuits _ (guard := fun _ => true)
    (ComputableInPolyTime.const true) (by simp) (8 * (Polynomial.X + 1) ^ 3) ?_
  intro out hout
  have ha : Accepts out := hout
  obtain ⟨gs, hcost, _, hlen, hsame⟩ :=
    Certificates.capped_certificate _ _ _ ha (synthesisBound out ha)
  refine ⟨gs, hcost, hsame, hlen.trans ?_⟩
  have hn : (decode out).qubits ≤ (encodeTy OutputTy out).length := out_qubits_le out
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  calc
    _ ≤ 8 * ((decode out).qubits + 1) ^ 3 := by nlinarith
    _ ≤ _ := by gcongr

end CliffordFrontier
