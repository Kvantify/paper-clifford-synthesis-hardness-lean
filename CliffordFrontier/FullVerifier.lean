/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.CliffordVerifier
public import CliffordFrontier.DecisionProblems
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin

/-!
# Full Verifier

Verification of phase-free circuits over a fixed two-qubit gate family.
The input and simulated tableau each contain all four Boolean matrix blocks.
-/

@[expose] public section

namespace CliffordFrontier

open CliffordComplexity Turing.MultiTapeTM CliffordSynthesis

namespace FullVerifier

open TwoQubit (Matrix Bits StepWithSwap)

local instance : Finite Matrix :=
  Finite.of_injective BitVec.toFin (fun _ _ h => BitVec.eq_of_toNat_eq (congrArg Fin.val h))

/-- Two tag bits select H, S, a paid two-qubit gate, or a free SWAP.
Wire indices are unary and the optional matrix is numbered in a fixed finite set. -/
abbrev RawStep := (Bool × Bool) × CNOTIndices × Nat

/-- The pair encoding of the two instruction selector bits. -/
abbrev encTag := encPair encBool encBool
/-- Encode an instruction’s selector, unary wires, and unary matrix key. -/
abbrev encRawStep : RawStep ↪ List Bool :=
  encPair encTag (encPair encCNOTIndices encUnary)
/-- Encode a list of raw phase-free instructions. -/
abbrev encWitness : List RawStep ↪ List Bool := encList encRawStep
/-- Pair the full-tableau instance encoding with the raw witness encoding. -/
abbrev encVerifierInput := encPair encFullTableauInput encWitness

/-- Decode a raw phase-free circuit certificate. -/
def decoder : Decoder encWitness :=
  Decoder.list (Decoder.pair (Decoder.pair Decoder.bool Decoder.bool)
    (Decoder.pair (Decoder.pair Decoder.unary Decoder.unary) Decoder.unary))

/-- Whether the gate tag denotes a two-qubit instruction counted against the budget. -/
def paid (raw : RawStep) : Bool := raw.1.1 && !raw.1.2

/-- Encode a typed gate or free SWAP as a raw phase-free instruction. -/
def encodeStep {n : Nat} : StepWithSwap n → RawStep
  | .gate (.H i) => ((false, false), (i.val, 0), 0)
  | .gate (.S i) => ((false, true), (i.val, 0), 0)
  | .gate (.two c t _ g) => ((true, false), (c.val, t.val), g.val.toNat)
  | .swap c t => ((true, true), (c.val, t.val), 0)

/-- The framed Boolean encoding of a four-bit vector. -/
abbrev encBits4 : Bits ↪ List Bool :=
  encPair encBool (encPair encBool (encPair encBool encBool))

/-- Encode a two-qubit symplectic matrix as its bounded unary key. -/
abbrev encMat : Matrix ↪ List Bool :=
  ⟨fun m => encUnary m.toNat, fun _ _ h => BitVec.eq_of_toNat_eq (encUnary.injective h)⟩

theorem matrix_polyTime :
    ComputableInPolyTime (BitVec.ofNat 16) encUnary encMat := by
  let enc : Fin (2 ^ 16) ↪ List Bool :=
    ⟨fun i => encUnary i.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩
  refine (ComputableInPolyTime.unary_finMod
    (bound := 2 ^ 16) (by decide) enc).of_enc_eq ?_
  intro _
  rfl

/-- Apply either a SWAP of the wire pair or its given symplectic matrix. -/
def pairAction (swapping : Bool) (m : Matrix) (v : Bits) : Bits :=
  if swapping then TwoQubit.swapAction v else TwoQubit.action m v

/-- Update two wires in one pair of X/Z blocks. -/
def applyPairBlocks (p : Blocks × CNOTIndices × Bool × Matrix) : Blocks :=
  let b := p.1
  let (c, t) := p.2.1
  let values j := pairAction p.2.2.1 p.2.2.2
    (entry b.1 c j, entry b.2 c j, entry b.1 t j, entry b.2 t j)
  (tabulate b.1.length fun i j =>
    if i = c then (values j).1 else if i = t then (values j).2.2.1 else entry b.1 i j,
   tabulate b.1.length fun i j =>
    if i = c then (values j).2.1 else if i = t then (values j).2.2.2 else entry b.2 i j)

/-- Encode the blocks and arguments to the two-wire action. -/
abbrev encPairBlocksInput := encPair encBlocks (encPair encCNOTIndices (encPair encBool encMat))

theorem applyPairBlocks_polyTime :
    ComputableInPolyTime applyPairBlocks encPairBlocksInput encBlocks := by
  let encOuter := encPair encPairBlocksInput encUnary
  have data := ComputableInPolyTime.fst encBlocks (encPair encCNOTIndices (encPair encBool encMat))
  have params := ComputableInPolyTime.snd encBlocks (encPair encCNOTIndices (encPair encBool encMat))
  have width := (ComputableInPolyTime.length_list (encList encBool)).comp data.fst'
  have outer := ComputableInPolyTime.fst encOuter encUnary
  have col := ComputableInPolyTime.snd encOuter encUnary
  have input := outer.fst'
  have row := outer.snd'
  have control := params.fst'.fst'.comp input
  have target := params.fst'.snd'.comp input
  have matrices := data.comp input
  have x := entry_polyTime matrices.fst' row col
  have z := entry_polyTime matrices.snd' row col
  have xc := entry_polyTime matrices.fst' control col
  have zc := entry_polyTime matrices.snd' control col
  have xt := entry_polyTime matrices.fst' target col
  have zt := entry_polyTime matrices.snd' target col
  have hAction : ComputableInPolyTime (fun q : (Bool × Matrix) × Bits =>
      pairAction q.1.1 q.1.2 q.2) (encPair (encPair encBool encMat) encBits4) encBits4 :=
    ComputableInPolyTime.of_finite _
  have updated := hAction.comp ((params.snd'.comp input).prod (xc.prod (zc.prod (xt.prod zt))))
  have isControl := row.decide_eq' control
  have isTarget := row.decide_eq' target
  have xPoly := isControl.ite updated.fst' (isTarget.ite updated.snd'.snd'.fst' x)
  have zPoly := isControl.ite updated.snd'.fst' (isTarget.ite updated.snd'.snd'.snd' z)
  exact (tabulate_polyTime width (by simpa only [Function.comp_apply, decide_eq_true_eq] using xPoly)).prod
    (tabulate_polyTime width (by simpa only [Function.comp_apply, decide_eq_true_eq] using zPoly))

/-- Update a packed phase-free tableau using one raw instruction. -/
def applyRawStep (p : PackedTableau × RawStep) : PackedTableau :=
  let (a, g) := p
  if g.1.1 then
    (applyPairBlocks (a.1, g.2.1, g.1.2, BitVec.ofNat 16 g.2.2),
     applyPairBlocks (a.2, g.2.1, g.1.2, BitVec.ofNat 16 g.2.2))
  else
    (applyLocalBlocks (a.1, g.1.2, g.2.1.1), applyLocalBlocks (a.2, g.1.2, g.2.1.1))

theorem applyRawStep_polyTime :
    ComputableInPolyTime applyRawStep (encPair encPackedTableau encRawStep) encPackedTableau := by
  have blocks := ComputableInPolyTime.fst encPackedTableau encRawStep
  have gate := ComputableInPolyTime.snd encPackedTableau encRawStep
  have phase := gate.fst'.snd'
  have indices := gate.snd'.fst'
  have mat := matrix_polyTime.comp gate.snd'.snd'
  have params := indices.prod (phase.prod mat)
  have leftPair := applyPairBlocks_polyTime.comp (blocks.fst'.prod params)
  have rightPair := applyPairBlocks_polyTime.comp (blocks.snd'.prod params)
  have localGate := phase.prod indices.fst'
  have leftLocal := applyLocalBlocks_polyTime.comp (blocks.fst'.prod localGate)
  have rightLocal := applyLocalBlocks_polyTime.comp (blocks.snd'.prod localGate)
  exact gate.fst'.fst'.ite (leftPair.prod rightPair) (leftLocal.prod rightLocal)

/-- A gate-family lookup on the fixed finite type of matrices. -/
noncomputable def matrixAllowed (Γ : Set TwoQubit.Gate) (m : Matrix) : Bool :=
  if h : TwoQubit.valid m = true then @decide (⟨m, h⟩ ∈ Γ) (Classical.propDecidable _) else false

theorem matrixAllowed_iff (Γ : Set TwoQubit.Gate) (m : Matrix) :
    matrixAllowed Γ m = true ↔ ∃ g ∈ Γ, g.val = m := by
  classical
  unfold matrixAllowed
  split
  next h =>
    rw [decide_eq_true_eq]
    constructor
    · intro hg
      exact ⟨⟨m, h⟩, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact hg
  next h =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨g, _, rfl⟩
    exact h g.property

/-- Validate the raw instruction’s tags, indices, and gate-family membership. -/
noncomputable def validStep (Γ : Set TwoQubit.Gate) (swaps : Bool) (n : Nat) (g : RawStep) : Bool :=
  if g.1.1 then
    if g.1.2 then swaps && decide (g.2.1.1 < n ∧ g.2.1.2 < n ∧ g.2.2 = 0)
    else validIndices n g.2.1 && decide (g.2.2 < 2 ^ 16) &&
      matrixAllowed Γ (BitVec.ofNat 16 g.2.2)
  else decide (g.2.1.1 < n ∧ g.2.1.2 = 0 ∧ g.2.2 = 0)

theorem validStep_polyTime (Γ : Set TwoQubit.Gate) (swaps : Bool) :
    ComputableInPolyTime (fun p : Nat × RawStep => validStep Γ swaps p.1 p.2)
      (encPair encUnary encRawStep) encBool := by
  have width := ComputableInPolyTime.fst encUnary encRawStep
  have gate := ComputableInPolyTime.snd encUnary encRawStep
  have indices := gate.snd'.fst'
  have key := gate.snd'.snd'
  have bound := ComputableTidilyInPolyTime.unary_lt' key.tidy
    (ComputableTidilyInPolyTime.const (2 ^ 16))
  have c := ComputableTidilyInPolyTime.unary_lt' indices.fst'.tidy width.tidy
  have t := ComputableTidilyInPolyTime.unary_lt' indices.snd'.tidy width.tidy
  have tZero := indices.snd'.decide_eq' (ComputableInPolyTime.const 0)
  have keyZero := key.decide_eq' (ComputableInPolyTime.const 0)
  have validTwo := validIndices_polyTime.comp (width.prod indices)
  have allowed : ComputableInPolyTime (matrixAllowed Γ) encMat encBool :=
    ComputableInPolyTime.of_finite _
  have hMat := allowed.comp (matrix_polyTime.comp key)
  have hSwap := (ComputableInPolyTime.const swaps).bool_and'
    (c.computableInPolyTime.bool_and' (t.computableInPolyTime.bool_and' keyZero))
  have hLocal := c.computableInPolyTime.bool_and' (tZero.bool_and' keyZero)
  have hTwo := (validTwo.bool_and' bound.computableInPolyTime).bool_and' hMat
  refine (gate.fst'.fst'.ite (gate.fst'.snd'.ite hSwap hTwo) hLocal).of_enc_eq ?_
  intro p
  simp [validStep, Function.comp_apply, Bool.decide_and]

/-- In the same typed model, either permit free swaps or require only ordinary gates. -/
def Allowed {n : Nat} (Γ : Set TwoQubit.Gate) (swaps : Bool) : StepWithSwap n → Prop
  | .gate g => TwoQubit.Allowed Γ g
  | .swap _ _ => swaps = true

theorem allowed_embed {n : Nat} (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (cs : List (TwoQubit.Step n)) :
    (∀ g ∈ cs.map StepWithSwap.gate, Allowed Γ swaps g) ↔
      ∀ g ∈ cs, TwoQubit.Allowed Γ g := by
  constructor
  · intro h g hg
    exact h (.gate g) (List.mem_map_of_mem hg)
  · intro h g hg
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
    exact h s hs

theorem valid_encodeStep {n : Nat} (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (g : StepWithSwap n) (h : Allowed Γ swaps g) : validStep Γ swaps n (encodeStep g) = true := by
  cases g with
  | swap c t =>
    simpa [validStep, encodeStep, Allowed, c.isLt, t.isLt] using h
  | gate g =>
    cases g with
    | H i => simp [validStep, encodeStep, i.isLt]
    | S i => simp [validStep, encodeStep, i.isLt]
    | two c t hct m =>
      have hn : c.val ≠ t.val := fun he => hct (Fin.ext he)
      have hm : matrixAllowed Γ m.val = true := (matrixAllowed_iff Γ _).mpr ⟨m, h, rfl⟩
      have hlt : m.val.toNat < 65536 := m.val.isLt
      simp [validStep, encodeStep, validIndices, c.isLt, t.isLt, hn, hm, hlt]

private theorem decode_step {n : Nat} (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (raw : RawStep) (h : validStep Γ swaps n raw = true) :
    ∃ g : StepWithSwap n, Allowed Γ swaps g ∧ encodeStep g = raw := by
  obtain ⟨⟨tag, flag⟩, ⟨c, t⟩, m⟩ := raw
  cases tag <;> cases flag
  · simp [validStep] at h
    obtain ⟨hc, rfl, rfl⟩ := h
    exact ⟨.gate (.H ⟨c, hc⟩), trivial, rfl⟩
  · simp [validStep] at h
    obtain ⟨hc, rfl, rfl⟩ := h
    exact ⟨.gate (.S ⟨c, hc⟩), trivial, rfl⟩
  · change (validIndices n (c, t) && decide (m < 2 ^ 16) &&
      matrixAllowed Γ (BitVec.ofNat 16 m)) = true at h
    simp only [validIndices, Bool.and_eq_true, decide_eq_true_eq, matrixAllowed_iff] at h
    obtain ⟨⟨⟨hc, ht, hct⟩, hm⟩, g, hg, he⟩ := h
    refine ⟨.gate (.two ⟨c, hc⟩ ⟨t, ht⟩ (fun h => hct (congrArg Fin.val h)) g), hg, ?_⟩
    dsimp [encodeStep]
    rw [he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]
  · simp [validStep, Bool.and_eq_true] at h
    obtain ⟨hs, hc, ht, rfl⟩ := h
    exact ⟨.swap ⟨c, hc⟩ ⟨t, ht⟩, hs, rfl⟩

private theorem decode_steps {n : Nat} (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (raw : List RawStep) (h : raw.all (validStep Γ swaps n) = true) :
    ∃ gs : List (StepWithSwap n), (∀ g ∈ gs, Allowed Γ swaps g) ∧ gs.map encodeStep = raw := by
  induction raw with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons raw rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨g, hg, rfl⟩ := decode_step Γ swaps raw h.1
    obtain ⟨gs, hgs, rfl⟩ := ih h.2
    exact ⟨g :: gs, List.forall_mem_cons.mpr ⟨hg, hgs⟩, rfl⟩

private def applyTypedStep {n : Nat} (g : StepWithSwap n) (a : Circuit.Tableau n) :
    Circuit.Tableau n :=
  match g with
  | .gate g => TwoQubit.applyStep g a
  | .swap c t => FreeSwaps.reorder (Equiv.swap c t) a

theorem applyPairBlocks_correct {n : Nat} (a : PackedTableau)
    (hx : a.1.1.length = n) (hz : a.2.1.length = n) (c t : Fin n) (swaps : Bool) (m : Matrix) :
    asPackedTableau n
        (applyPairBlocks (a.1, (c.val, t.val), swaps, m),
         applyPairBlocks (a.2, (c.val, t.val), swaps, m)) =
      TwoQubit.update c t (pairAction swaps m) (asPackedTableau n a) := by
  apply FreeLayers.tableau_ext
  intro i p
  rcases p with ⟨j, b⟩
  cases b <;>
    simp [FreeLayers.pair, asPackedTableau, applyPairBlocks, hx, hz,
      entry_tabulate, TwoQubit.update, TwoQubit.read, ← Fin.val_inj]

theorem update_swap {n : Nat} (a : Circuit.Tableau n) (c t : Fin n) :
    TwoQubit.update c t TwoQubit.swapAction a = FreeSwaps.reorder (Equiv.swap c t) a := by
  by_cases h : c = t
  · subst t
    apply FreeLayers.tableau_ext
    intro i p
    by_cases hi : i = c <;>
      simp [FreeLayers.pair, TwoQubit.update, TwoQubit.swapAction, TwoQubit.read, FreeSwaps.reorder, hi]
  · exact (TwoQubit.swap_update c t h a).symm

private theorem applyRawStep_correct {n : Nat} (a : PackedTableau)
    (hx : a.1.1.length = n) (hz : a.2.1.length = n) (g : StepWithSwap n) :
    asPackedTableau n (applyRawStep (a, encodeStep g)) =
      applyTypedStep g (asPackedTableau n a) := by
  cases g with
  | swap c t =>
    change asPackedTableau n (applyPairBlocks (a.1, (c.val, t.val), true, 0),
      applyPairBlocks (a.2, (c.val, t.val), true, 0)) = FreeSwaps.reorder (Equiv.swap c t)
        (asPackedTableau n a)
    exact (applyPairBlocks_correct a hx hz c t true 0).trans (update_swap _ c t)
  | gate g =>
    cases g with
    | H i =>
      apply FreeLayers.tableau_ext
      intro q p
      have h := applyCliffordBlocks_correct a hx hz (.H i) q p
      simpa [applyRawStep, encodeStep, applyCliffordBlocks, encodeCliffordGate,
        applyTypedStep, TwoQubit.applyStep, Circuit.applyGate, FreeLayers.pair, Prod.ext_iff] using h
    | S i =>
      apply FreeLayers.tableau_ext
      intro q p
      have h := applyCliffordBlocks_correct a hx hz (.S i) q p
      simpa [applyRawStep, encodeStep, applyCliffordBlocks, encodeCliffordGate,
        applyTypedStep, TwoQubit.applyStep, Circuit.applyGate, FreeLayers.pair, Prod.ext_iff] using h
    | two c t hct m =>
      have hm : BitVec.ofNat 16 m.val.toNat = m.val := by simp
      change asPackedTableau n
        (applyPairBlocks (a.1, (c.val, t.val), false, BitVec.ofNat 16 m.val.toNat),
         applyPairBlocks (a.2, (c.val, t.val), false, BitVec.ofNat 16 m.val.toNat)) = _
      rw [hm]
      exact applyPairBlocks_correct a hx hz c t false m.val

/-- Each block is a square Boolean matrix of the prescribed width. -/
def PackedSquare (n : Nat) (a : PackedTableau) : Prop :=
  Square n a.1.1 ∧ Square n a.1.2 ∧ Square n a.2.1 ∧ Square n a.2.2

theorem identity_square (n : Nat) : PackedSquare n (identityPacked n) := by
  simp [PackedSquare, identityPacked, identityBlocks, zeroMatrix, tabulate_square]

theorem packed_encoded_size {n : Nat} {a : PackedTableau} (h : PackedSquare n a) :
    (encPackedTableau a).length ≤ 64 * (n + 1) ^ 2 := by
  obtain ⟨hxx, hzx, hxz, hzz⟩ := h
  have h₁ := square_encoded_size hxx
  have h₂ := square_encoded_size hzx
  have h₃ := square_encoded_size hxz
  have h₄ := square_encoded_size hzz
  simp only [encPackedTableau, encBlocks, length_encPair]
  nlinarith

theorem applyPairBlocks_square (n : Nat) (a : PackedTableau) (indices : CNOTIndices)
    (swaps : Bool) (m : Matrix) (h : PackedSquare n a) :
    PackedSquare n (applyPairBlocks (a.1, indices, swaps, m),
      applyPairBlocks (a.2, indices, swaps, m)) := by
  simp [PackedSquare, applyPairBlocks, h.1.1, h.2.2.1.1, tabulate_square]

private theorem step_square (n : Nat) (a : PackedTableau) (g : RawStep)
    (hx : a.1.1.length = n) (hz : a.2.1.length = n) :
    PackedSquare n (applyRawStep (a, g)) := by
  rcases g with ⟨⟨tag, flag⟩, g⟩
  cases tag <;>
    simp [PackedSquare, applyRawStep, applyPairBlocks, applyLocalBlocks, hx, hz, tabulate_square]

private theorem run_raw_steps {n : Nat} (a : PackedTableau)
    (h : PackedSquare n a) (gs : List (StepWithSwap n)) :
    asPackedTableau n ((gs.map encodeStep).foldl
      (fun state g => applyRawStep (state, g)) a) =
      StepWithSwap.run gs (asPackedTableau n a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ih _ (step_square n a (encodeStep g) h.1.1 h.2.2.1.1)]
    rw [applyRawStep_correct a h.1.1 h.2.2.1.1 g]
    cases g <;> rfl

private theorem count_paid {n : Nat} (gs : List (StepWithSwap n)) :
    (gs.map encodeStep).countP paid = StepWithSwap.cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | swap c t => simpa [paid, encodeStep, StepWithSwap.cost] using ih
    | gate g =>
      cases g <;> simp [paid, encodeStep, StepWithSwap.cost, TwoQubit.paid, ih, Nat.add_comm]

theorem comparePacked_correct (n : Nat) (a b : PackedTableau) :
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

/-- Arrange the four blocks of the input in simulator order. -/
def targetPacked (out : FullTableauInput) : PackedTableau :=
  ((out.1.1, out.2.1.1), (out.1.2, out.2.1.2))

theorem target_correct (out : FullTableauInput) :
    asPackedTableau out.1.1.length (targetPacked out) = (decodeFull out).tableau := by
  apply FreeLayers.tableau_ext
  intro i p
  rcases p with ⟨j, b⟩
  cases b <;>
    simp [FreeLayers.pair, asPackedTableau, targetPacked, decodeFull, entry,
      MatrixCompiler.readBit, List.getD_eq_getElem?_getD]

theorem targetPacked_polyTime : ComputableInPolyTime targetPacked encFullTableauInput
    encPackedTableau := by
  let p := ComputableInPolyTime.fst encBlocks (encPair encBlocks encNat)
  let q := (ComputableInPolyTime.snd encBlocks (encPair encBlocks encNat)).fst'
  exact (p.fst'.prod q.fst').prod (p.snd'.prod q.snd')

/-- Verify the budget, gate eligibility, and full phase-free tableau of a witness. -/
noncomputable def check (Γ : Set TwoQubit.Gate) (swaps : Bool)
    (x : FullTableauInput × List RawStep) : Bool :=
  let out := x.1
  let n := out.1.1.length
  let result := x.2.foldl (fun state g => applyRawStep (state, g)) (identityPacked n)
  decide (x.2.countP paid ≤ out.2.2) && x.2.all (validStep Γ swaps n) &&
    comparePacked n result (targetPacked out)

private theorem check_encoded_iff (Γ : Set TwoQubit.Gate) (swaps : Bool) (out : FullTableauInput)
    (gs : List (StepWithSwap (decodeFull out).qubits)) (ha : ∀ g ∈ gs, Allowed Γ swaps g) :
    check Γ swaps (out, gs.map encodeStep) = true ↔
      StepWithSwap.cost gs ≤ (decodeFull out).threshold ∧
      Circuit.Same (StepWithSwap.run gs (Circuit.identity (decodeFull out).qubits))
        (decodeFull out).tableau := by
  have hv : (gs.map encodeStep).all (validStep Γ swaps out.1.1.length) = true := by
    apply List.all_eq_true.mpr
    intro raw hraw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hraw
    exact valid_encodeStep Γ swaps g (ha g hg)
  have hr := run_raw_steps (identityPacked out.1.1.length) (identity_square _) gs
  rw [identityPacked_correct] at hr
  simp only [check, Bool.and_eq_true, comparePacked_correct]
  change ((decide ((gs.map encodeStep).countP paid ≤ out.2.2) = true ∧
    (gs.map encodeStep).all (validStep Γ swaps out.1.1.length) = true) ∧
      Circuit.Same _ (asPackedTableau out.1.1.length (targetPacked out))) ↔ _
  rw [decide_eq_true_eq, count_paid, hv, target_correct]
  simp only [and_true]
  exact and_congr_right (fun _ => Iff.of_eq (congrArg
    (fun a : Circuit.Tableau out.1.1.length => Circuit.Same a (decodeFull out).tableau) hr))

/-- The phase-free synthesis language witnessed by lists of allowed typed steps. -/
def language (Γ : Set TwoQubit.Gate) (swaps : Bool) : Set FullTableauInput :=
  {out | ∃ gs : List (StepWithSwap (decodeFull out).qubits),
    (∀ g ∈ gs, Allowed Γ swaps g) ∧ StepWithSwap.cost gs ≤ (decodeFull out).threshold ∧
    Circuit.Same (StepWithSwap.run gs (Circuit.identity (decodeFull out).qubits))
      (decodeFull out).tableau}

private theorem check_sound (Γ : Set TwoQubit.Gate) (swaps : Bool) (out : FullTableauInput)
    (raw : List RawStep) (h : check Γ swaps (out, raw) = true) : out ∈ language Γ swaps := by
  have hv : raw.all (validStep Γ swaps (decodeFull out).qubits) = true := by
    simp only [check, Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨gs, ha, rfl⟩ := decode_steps Γ swaps raw hv
  obtain ⟨hc, hs⟩ := (check_encoded_iff Γ swaps out gs ha).mp h
  exact ⟨gs, ha, hc, hs⟩

theorem width_bound (out : FullTableauInput) :
    (decodeFull out).qubits ≤ (encFullTableauInput out).length := by
  let tail := encPair encBlocks encNat
  change out.1.1.length ≤ (encPair encBlocks tail out).length
  apply (length_le_length_encList (encList encBool) out.1.1).trans
  exact (length_le_encPair_left encMatrix encMatrix out.1).trans
    (length_le_encPair_left encBlocks tail out)

private theorem fold_square (n : Nat) (gs : List RawStep) (a : PackedTableau)
    (ha : PackedSquare n a) :
    PackedSquare n (gs.foldl (fun state g => applyRawStep (state, g)) a) := by
  induction gs generalizing a with
  | nil => exact ha
  | cons g gs ih => exact ih _ (step_square n a g ha.1.1 ha.2.2.1.1)

private theorem fold_size (x : FullTableauInput × List RawStep) (i : Nat) :
    (encPackedTableau ((x.2.take i).foldl (fun state g => applyRawStep (state, g))
      (identityPacked x.1.1.1.length))).length ≤ 64 * (x.1.1.1.length + 1) ^ 2 := by
  exact packed_encoded_size (fold_square _ (x.2.take i) _ (identity_square _))

theorem check_polyTime (Γ : Set TwoQubit.Gate) (swaps : Bool) :
    ComputableInPolyTime (check Γ swaps) encVerifierInput encBool := by
  let eOut := encPair encBlocks (encPair encBlocks encNat)
  have out := ComputableTidilyInPolyTime.fst eOut encWitness
  have witness := ComputableTidilyInPolyTime.snd eOut encWitness
  have width := (ComputableTidilyInPolyTime.length_list (encList encBool)).comp out.fst'.fst'
  have threshold := out.snd'.snd'
  have run := ComputableTidilyInPolyTime.foldl'
    (step := fun state g => applyRawStep (state, g))
    witness (identityPacked_polyTime.tidy.comp width) applyRawStep_polyTime.tidy
    (B := fun x => 64 * (x.1.1.1.length + 1) ^ 2)
    (.of_forall_le 64 2 fun x =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right ((width_bound x.1).trans
          (length_le_encPair_left eOut encWitness x)) 1) 2))
    (fun x i _ => fold_size x i)
  have target := targetPacked_polyTime.tidy.comp out
  have compare := comparePacked_polyTime.tidy.comp (width.prod (run.prod target))
  have valid := ComputableTidilyInPolyTime.allWith (validStep_polyTime Γ swaps).tidy width witness
  have paidTag : ComputableTidilyInPolyTime (fun t : Bool × Bool => t.1 && !t.2) encTag encBool :=
    ComputableTidilyInPolyTime.of_finite _
  have count := ComputableTidilyInPolyTime.countPWithInput (test := fun _ g => paid g) witness
    (paidTag.comp (ComputableTidilyInPolyTime.snd encVerifierInput encRawStep).fst')
  have bound := ComputableTidilyInPolyTime.binary_le.comp
    ((ComputableTidilyInPolyTime.unary_to_binary.comp count).prod threshold)
  exact (bound.bool_and' valid |>.bool_and' compare).computableInPolyTime

private theorem encodeStep_size {n : Nat} (g : StepWithSwap n) :
    2 * (encRawStep (encodeStep g)).length + 1 ≤ 262200 * (n + 1) := by
  cases g with
  | swap c t =>
    simp [encRawStep, encTag, encCNOTIndices, encodeStep, encBool_apply, encUnary_apply]
    omega
  | gate g =>
    cases g with
    | H i =>
      simp [encRawStep, encTag, encCNOTIndices, encodeStep, encBool_apply, encUnary_apply]
      omega
    | S i =>
      simp [encRawStep, encTag, encCNOTIndices, encodeStep, encBool_apply, encUnary_apply]
      omega
    | two c t h m =>
      have hm : m.val.toNat < 2 ^ 16 := m.val.isLt
      simp [encRawStep, encTag, encCNOTIndices, encodeStep, encBool_apply, encUnary_apply]
      omega

private theorem encode_word_size {n : Nat} (gs : List (StepWithSwap n)) :
    (encWitness (gs.map encodeStep)).length ≤ gs.length * (262200 * (n + 1)) := by
  rw [length_encList]
  simp only [List.map_map]
  refine (List.sum_le_length_nsmul _ (262200 * (n + 1)) ?_).trans ?_
  · intro m hm
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hm
    exact encodeStep_size g
  · simp

theorem mem_NP_of_short (Γ : Set TwoQubit.Gate) (swaps : Bool) (p : Polynomial Nat)
    (short : ∀ out ∈ language Γ swaps, ∃ gs : List (StepWithSwap (decodeFull out).qubits),
      (∀ g ∈ gs, Allowed Γ swaps g) ∧ StepWithSwap.cost gs ≤ (decodeFull out).threshold ∧
      Circuit.Same (StepWithSwap.run gs (Circuit.identity (decodeFull out).qubits))
        (decodeFull out).tableau ∧ gs.length ≤ p.eval (encFullTableauInput out).length) :
    language Γ swaps ∈ Cslib.Complexity.NP encFullTableauInput := by
  apply Cslib.Complexity.mem_NP_of_check (p := p * (262200 * (Polynomial.X + 1)))
    decoder (check_polyTime Γ swaps)
  · exact check_sound Γ swaps
  · intro out hout
    obtain ⟨gs, ha, hc, hs, hlen⟩ := short out hout
    refine ⟨gs.map encodeStep, (check_encoded_iff Γ swaps out gs ha).mpr ⟨hc, hs⟩, ?_⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    exact (encode_word_size gs).trans (Nat.mul_le_mul hlen
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (width_bound out) 1)))

end FullVerifier
end CliffordFrontier
