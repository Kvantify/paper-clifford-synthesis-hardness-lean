/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FullSynthesisBound
public import CliffordSynthesis.FullSynthesisPermutations
public import CliffordSynthesis.SignedProjection
public import CliffordSynthesis.Certificates

/-!
# Full Synthesis Signed

Set the signs on the input generators and then run a bounded linear synthesis.
-/

@[expose] public section

namespace CliffordSynthesis.SignedCircuit

variable {n : Nat}

private def liftGate : Circuit.Gate n → Step n
  | .H i => .single i (1, false, false)
  | .S i => .single i (2, false, false)
  | .CX c t hct => .two c t hct cnotGate

private theorem liftGate_linear (g : Circuit.Gate n) (T : Tableau n) :
    (applyStep (liftGate g) T).linear = Circuit.applyGate g T.linear := by
  cases g with
  | H q =>
      apply FreeLayers.tableau_ext
      intro i p
      by_cases h : i = q <;>
        simp [liftGate, applyStep, Circuit.applyGate, FreeLayers.applyFrames, FreeLayers.pair,
          Circuit.hadamard, h, FreeLayers.act]
  | S q =>
      apply FreeLayers.tableau_ext
      intro i p
      by_cases h : i = q <;>
        simp [liftGate, applyStep, Circuit.applyGate, FreeLayers.applyFrames, FreeLayers.pair,
          Circuit.phase, h, FreeLayers.act]
  | CX c t hct =>
      change TwoQubit.update c t (TwoQubit.action TwoQubit.cnotGate.val) T.linear =
        Circuit.cnot c t T.linear
      rw [funext TwoQubit.cnotGate_action, TwoQubit.cnot_update _ _ hct]

private theorem lift_run_linear (gs : List (Circuit.Gate n)) (T : Tableau n) :
    (run (gs.map liftGate) T).linear = Circuit.run gs T.linear := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.map_cons, run, Circuit.run, ih, liftGate_linear]

private theorem lift_allowed (Γ : Set TwoGate) (hΓ : cnotGate ∈ Γ) (swaps : Bool)
    (gs : List (Circuit.Gate n)) (g : Step n) (hg : g ∈ gs.map liftGate) :
    g.allowed Γ swaps := by
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
  cases g with
  | H => trivial
  | S => trivial
  | CX => exact hΓ

private theorem run_cat (gs hs : List (Step n)) (T : Tableau n) :
    run (gs ++ hs) T = run hs (run gs T) := by
  induction gs generalizing T with
  | nil => rfl
  | cons g gs ih => exact ih _

private theorem xor_repeat : ∀ x y z : Bool, ((x ^^ z) ^^ (y ^^ z)) = (x ^^ y) := by decide

private theorem xor_cancel_right : ∀ x y z : Bool, (x ^^ y) = (y ^^ z) → x = z := by decide

/-- The relative input sign of each generator is unchanged through a fixed circuit. -/
private theorem run_sign_diff (gs : List (Step n)) (T U : Tableau n) (hl : T.linear = U.linear)
    (p : Fin n × Bool) :
    ((run gs T).sign p ^^ (run gs U).sign p) = (T.sign p ^^ U.sign p) := by
  induction gs generalizing T U with
  | nil => rfl
  | cons g gs ih =>
      have hstep : (applyStep g T).linear = (applyStep g U).linear := by
        cases g <;> simp [applyStep, hl]
      rw [run, run, ih _ _ hstep]
      cases g <;> simp only [applyStep, hl, xor_repeat]

private def setInputSign (f : Fin n × Bool → Bool) (i : Fin n) : Step n :=
  .single i (0, f (i, false), f (i, true))

private theorem setInputSign_linear (f : Fin n × Bool → Bool) (i : Fin n) (T : Tableau n) :
    (applyStep (setInputSign f i) T).linear = T.linear := by
  change FreeLayers.applyFrames (Function.update (fun _ => 0) i 0) T.linear = T.linear
  have h : Function.update (fun _ : Fin n => (0 : Fin 6)) i 0 = fun _ => 0 := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [h, FreeLayers.frames_zero]

private theorem identity_signChange_zero :
    ∀ bx bz : Bool, signChange (TwoQubit.localAction 0 0)
      (bx, bz, false, false) (false, false, false, false) = false := by decide

private theorem identity_signChange_basis :
    ∀ bx bz b : Bool, signChange (TwoQubit.localAction 0 0)
      (bx, bz, false, false) (!b, b, false, false) = (if b then bz else bx) := by decide

private theorem setInputSign_sign (f : Fin n × Bool → Bool) (i : Fin n) (T : Tableau n)
    (hl : T.linear = Circuit.identity n) (p : Fin n × Bool) :
    (applyStep (setInputSign f i) T).sign p =
      (T.sign p ^^ if p.1 = i then f p else false) := by
  rcases p with ⟨j, b⟩
  unfold setInputSign applyStep
  by_cases h : j = i
  · subst j
    cases b <;> simp [FreeLayers.pair, hl, Circuit.identity]
    · exact identity_signChange_basis _ _ false
    · exact identity_signChange_basis _ _ true
  · simp [FreeLayers.pair, hl, Circuit.identity, h, Ne.symm h, identity_signChange_zero]

private theorem setInputSigns_run (f : Fin n × Bool → Bool) (qs : List (Fin n))
    (hq : qs.Nodup) (T : Tableau n) (hl : T.linear = Circuit.identity n) :
    (run (qs.map (setInputSign f)) T).linear = Circuit.identity n ∧
      ∀ p, (run (qs.map (setInputSign f)) T).sign p =
        (T.sign p ^^ if p.1 ∈ qs then f p else false) := by
  induction qs generalizing T with
  | nil => simp [run, hl]
  | cons i qs ih =>
      rw [List.nodup_cons] at hq
      simp only [List.map_cons, run]
      obtain ⟨hlinear, hsign⟩ := ih hq.2 (applyStep (setInputSign f i) T)
        ((setInputSign_linear f i T).trans hl)
      refine ⟨hlinear, fun p => ?_⟩
      rw [hsign, setInputSign_sign f i T hl]
      by_cases he : p.1 = i
      · simp [he, hq.1]
      · simp [he]

private theorem cost_le_length (a b : Nat) (gs : List (Step n)) :
    cost a b gs ≤ (a + b) * gs.length := by
  induction gs with
  | nil => simp [cost]
  | cons g gs ih =>
      have hw : g.weight a b ≤ a + b := by cases g <;> simp [Step.weight]
      simp only [cost, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem columnsSymplectic_run {T : Tableau n} (ha : Circuit.ColumnsSymplectic T.linear)
    (gs : List (Step n)) : Circuit.ColumnsSymplectic (run gs T).linear := by
  obtain ⟨ss, _, h⟩ := forget_signs 0 0 gs
  rw [← h T]
  exact TwoQubit.StepWithSwap.columnsSymplectic_run ha ss

/-- A polynomial bound on the total cost of a signed synthesis over a family containing CNOT. -/
def fullSynthesisCap (a b n : Nat) : Nat := (a + b) * (n + 3 * n * (n ^ 2 + 1) + n ^ 2)

theorem full_synthesis_bound_of_symplectic (Γ : Set TwoGate) (a b : Nat) (swaps : Bool)
    (hΓ : cnotGate ∈ Γ) (target : Tableau n) (h : Circuit.ColumnsSymplectic target.linear) :
    Synthesizes Γ a b swaps target (fullSynthesisCap a b n) := by
  obtain ⟨gs, hcost, hsame⟩ := Circuit.full_synthesis_bound_of_symplectic target.linear h
  obtain ⟨cs, _, hlen, hrun⟩ := Certificates.normalize gs
  have hlen' : cs.length ≤ 3 * n * (n ^ 2 + 1) + n ^ 2 := by
    unfold Circuit.fullSynthesisCap at hcost
    exact hlen.trans (by gcongr)
  let lifted := cs.map liftGate
  let base := run lifted (identity n)
  let f := fun p => base.sign p ^^ target.sign p
  let initial := (List.finRange n).map (setInputSign f)
  obtain ⟨hl, hs⟩ := setInputSigns_run f (List.finRange n) (List.nodup_finRange n) (identity n) rfl
  refine ⟨initial ++ lifted, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      trivial
    · exact lift_allowed Γ hΓ swaps cs g hg
  · refine (cost_le_length a b _).trans (Nat.mul_le_mul_left (a + b) ?_)
    simp only [List.length_append, List.length_map, List.length_finRange, initial, lifted]
    omega
  · rw [run_cat]
    refine ⟨?_, fun p => ?_⟩
    · change Circuit.Same (run (cs.map liftGate) (run initial (identity n))).linear target.linear
      rw [lift_run_linear, hl, hrun]
      exact hsame
    · have hd := run_sign_diff lifted (run initial (identity n)) (identity n) hl p
      have hs' : (run initial (identity n)).sign p = f p := by
        simpa [identity] using hs p
      rw [hs'] at hd
      change (_ ^^ base.sign p) = (f p ^^ false) at hd
      rw [Bool.xor_false] at hd
      exact xor_cancel_right _ _ _ hd

theorem full_synthesis_bound (Γ : Set TwoGate) (a b : Nat) (swaps : Bool)
    (hΓ : cnotGate ∈ Γ) (target : Tableau n) (k : Nat) (h : Synthesizes Γ a b swaps target k) :
    Synthesizes Γ a b swaps target (fullSynthesisCap a b n) := by
  obtain ⟨gs, _, _, hsame, _⟩ := h
  have ht : (run gs (identity n)).linear = target.linear :=
    FreeLayers.tableau_ext fun i p => Prod.ext (hsame i p).1 (hsame i p).2
  have hcols := columnsSymplectic_run (T := identity n) (Circuit.columnsSymplectic_identity n) gs
  rw [ht] at hcols
  exact full_synthesis_bound_of_symplectic Γ a b swaps hΓ target hcols

end CliffordSynthesis.SignedCircuit
