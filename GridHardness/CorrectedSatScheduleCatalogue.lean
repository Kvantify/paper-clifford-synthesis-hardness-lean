/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryProgram

/-!
# Corrected SAT Schedule Catalogue

Compile an explicit crossing catalogue into the insertion order.
The compiler uses only finite list filters; it is independent of any formula
assignment and names residual bundles rather than serial XOR-wire sections.
-/

@[expose] public section

namespace GridHardness.CorrectedSatSchedule
open XorLineRegistry

def chosen {B : Type} (cells : List (Nat × Nat)) (j : Nat) (old : B → Nat) (enum : List B) : List B :=
  enum.filter (fun b => decide ((old b,j) ∈ cells))

def compile (cells : List (Nat × Nat)) : (n j : Nat) → {B : Type} →
    (B → Nat) → List B → Program n B
  | 0, _, _, _, _ => .done
  | n+1, j, _, old, enum => .insert (chosen cells j old enum)
      (compile cells n (j+1) (fun b => Option.elim b j old) (none :: enum.map some))

def trace {B : Type} (cells : List (Nat × Nat)) (n j : Nat) (old : B → Nat) (enum : List B) :=
  (compile cells n j old enum).trace (fun i => j+i.val) old

theorem trace_succ {B : Type} (cells : List (Nat × Nat)) (n j : Nat) (old : B → Nat) (enum : List B) :
    trace cells (n+1) j old enum =
      (chosen cells j old enum).map (fun b => (old b,j)) ++
        trace cells n (j+1) (fun b => Option.elim b j old) (none::enum.map some) := by
  unfold trace
  simp only [compile,Program.trace,Fin.val_zero,Nat.add_zero,Fin.val_succ]
  congr 2
  funext i
  omega

/-- The finite enumeration records exactly the previously inserted labels. -/
def Enumerates {B : Type} (j : Nat) (old : B → Nat) (enum : List B) : Prop :=
  ∀ i, (∃ b ∈ enum, old b=i) ↔ i<j

theorem enumerates_next {B : Type} (j : Nat) (old : B → Nat) (enum : List B)
    (h : Enumerates j old enum) : Enumerates (j+1) (fun b => Option.elim b j old) (none::enum.map some) := by
  intro i
  constructor
  · rintro ⟨b,hb,hi⟩
    cases b with
    | none => change j=i at hi; omega
    | some b =>
      have hb' : b∈enum := by simpa using hb
      have hi' : old b=i := hi
      have := (h i).mp ⟨b,hb',hi'⟩
      omega
  · intro hi
    by_cases hij : i=j
    · exact ⟨none,List.mem_cons_self,by simpa using hij.symm⟩
    · obtain ⟨b,hb,hi'⟩ := (h i).mpr (by omega)
      exact ⟨some b,by simp [hb],hi'⟩

theorem mem_chosen_pairs {B : Type} (cells : List (Nat × Nat)) (j : Nat)
    (old : B → Nat) (enum : List B) (h : Enumerates j old enum) (p : Nat × Nat) :
    p ∈ (chosen cells j old enum).map (fun b => (old b,j)) ↔
      p∈cells ∧ p.1<j ∧ p.2=j := by
  rcases p with ⟨i,k⟩
  simp only [List.mem_map]
  constructor
  · rintro ⟨b,hb,hp⟩
    obtain ⟨hb,hc⟩ := List.mem_filter.mp hb
    have hc' : (old b,j)∈cells := of_decide_eq_true hc
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    exact ⟨hc',(h _).mp ⟨b,hb,rfl⟩,rfl⟩
  · rintro ⟨hp,hi,rfl⟩
    obtain ⟨b,hb,he⟩ := (h i).mpr hi
    exact ⟨b,List.mem_filter.mpr ⟨hb,by simpa [he] using hp⟩,Prod.ext he rfl⟩

/-- Every catalogue crossing whose later endpoint lies in the processed range
is executed. No crossing outside the catalogue is introduced. -/
theorem mem_trace (cells : List (Nat × Nat)) (n : Nat) :
    ∀ (j : Nat) {B : Type} (old : B → Nat) (enum : List B),
      Enumerates j old enum → ∀ p : Nat×Nat,
      p∈trace cells n j old enum ↔
        p∈cells ∧ p.1<p.2 ∧ j≤p.2 ∧ p.2<j+n := by
  induction n with
  | zero =>
    intro j B old enum h p
    simp only [trace,compile,Program.trace,List.not_mem_nil,false_iff,Nat.add_zero]
    omega
  | succ n ih =>
    intro j B old enum h p
    rw [trace_succ,List.mem_append,mem_chosen_pairs cells j old enum h p,
      ih (j+1) _ _ (enumerates_next j old enum h)]
    constructor
    · rintro (⟨hc,hi,hj⟩ | ⟨hc,hi,hj,hk⟩)
      · exact ⟨hc,by omega,by omega,by omega⟩
      · exact ⟨hc,hi,by omega,by omega⟩
    · rintro ⟨hc,hi,hj,hk⟩
      by_cases he : p.2=j
      · exact Or.inl ⟨hc,by omega,he⟩
      · exact Or.inr ⟨hc,hi,by omega,by omega⟩

/-- At most one move per prior label and insertion stage. The quadratic bound
does not depend on variable magnitudes or on binary-encoded loop bounds. -/
theorem length_le (cells : List (Nat × Nat)) (n : Nat) :
    ∀ (j : Nat) {B : Type} (old : B → Nat) (enum : List B), enum.length=j →
      (compile cells n j old enum).length ≤ n*(j+n) := by
  induction n with
  | zero => intro j B old enum h; simp [compile,Program.length]
  | succ n ih =>
    intro j B old enum h
    have hnext : (none::enum.map some).length=j+1 := by simp [h]
    have htail := ih (j+1) (fun b => Option.elim b j old) (none::enum.map some) hnext
    have hchosen : (chosen cells j old enum).length≤j := by
      exact (List.length_filter_le _ _).trans_eq h
    change (chosen cells j old enum).length+(compile cells n (j+1) _ _).length≤_
    nlinarith

theorem chosen_pairs_nodup {B : Type} (cells : List (Nat × Nat)) (j : Nat)
    (old : B → Nat) (enum : List B) (hn : (enum.map old).Nodup) :
    ((chosen cells j old enum).map (fun b => (old b,j))).Nodup := by
  have hsub : (chosen cells j old enum).Sublist enum := List.filter_sublist
  have hh := hn.sublist (hsub.map old)
  have hp : (((chosen cells j old enum).map old).map (fun i => (i,j))).Nodup :=
    List.Nodup.map_on (fun i _ k _ he => (Prod.mk.inj he).1) hh
  simpa only [List.map_map,Function.comp_def] using hp

theorem trace_nodup (cells : List (Nat × Nat)) (n : Nat) :
    ∀ (j : Nat) {B : Type} (old : B → Nat) (enum : List B),
      Enumerates j old enum → (enum.map old).Nodup → (trace cells n j old enum).Nodup := by
  induction n with
  | zero => intro j B old enum h hn; simp [trace,compile,Program.trace]
  | succ n ih =>
    intro j B old enum h hn
    have hnnext : ((none::enum.map some).map (fun b => Option.elim b j old)).Nodup := by
      have hcons : (j::enum.map old).Nodup := by
        apply List.nodup_cons.mpr
        refine ⟨?_,hn⟩
        intro hm
        obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
        have := (h j).mp ⟨b,hb,he⟩
        omega
      simpa only [List.map_cons,List.map_map,Function.comp_def,Option.elim] using hcons
    rw [trace_succ,List.nodup_append]
    refine ⟨chosen_pairs_nodup cells j old enum hn,
      ih (j+1) _ _ (enumerates_next j old enum h) hnnext,?_⟩
    intro p hp q hq he
    have hp' := (mem_chosen_pairs cells j old enum h p).mp hp
    have hq' := (mem_trace cells n (j+1) _ _ (enumerates_next j old enum h) q).mp hq
    have he' := congrArg Prod.snd he
    omega

/-- A completely specified plan for `N` original lines and a finite catalogue. -/
def plan (N : Nat) (cells : List (Nat × Nat)) : Program N Empty :=
  compile cells N 0 Empty.elim []

theorem mem_plan_trace (N : Nat) (cells : List (Nat × Nat)) (p : Nat × Nat) :
    p ∈ (plan N cells).trace Fin.val Empty.elim ↔
      p∈cells ∧ p.1<p.2 ∧ p.2<N := by
  have he : Enumerates 0 (Empty.elim : Empty → Nat) [] := by
    intro i
    simp
  have h := mem_trace cells N 0 Empty.elim [] he p
  simpa [plan,trace] using h

theorem plan_length_le (N : Nat) (cells : List (Nat × Nat)) : (plan N cells).length≤N*N := by
  simpa [plan] using length_le cells N 0 Empty.elim [] rfl

theorem plan_trace_nodup (N : Nat) (cells : List (Nat × Nat)) :
    ((plan N cells).trace Fin.val Empty.elim).Nodup := by
  have he : Enumerates 0 (Empty.elim : Empty → Nat) [] := by intro i; simp
  simpa [plan,trace] using trace_nodup cells N 0 Empty.elim [] he (by simp)

end GridHardness.CorrectedSatSchedule
