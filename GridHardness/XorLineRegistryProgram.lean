/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryRetire
public import GridHardness.XorLineScheduleRun

/-!
# XOR Line Registry Program

Execute a bounded insertion plan on actual finite graphs. Each inserted
line crosses a list of already processed bundles and is then retired.
-/

@[expose] public section

namespace GridHardness.XorLineRegistry
open XorLineSchedule

structure State (X B : Type) extends FiniteGraph where
  registry : Registry adj X B

namespace State
variable {X B : Type}

instance (s : State X B) : Finite s.Vertex := s.finite

def cross [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) (b : B) : State X B where
  Vertex := s.registry.CrossVertex a b
  finite := inferInstance
  adj := s.registry.crossAdj a b
  registry := s.registry.cross a b

theorem cross_correct [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) (b : B) :
    PathCover.Hamiltonian s.adj ↔ PathCover.Hamiltonian (s.cross a b).adj :=
  s.registry.cross_correct a b

theorem cross_vertex_count [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) (b : B) :
    Nat.card (s.cross a b).Vertex=Nat.card s.Vertex+40 :=
  s.registry.cross_vertex_count a b

def crossMany [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) : List B → State X B
  | [] => s
  | b::bs => crossMany (s.cross a b) a bs

theorem crossMany_correct [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) (bs : List B) :
    PathCover.Hamiltonian s.adj ↔ PathCover.Hamiltonian (s.crossMany a bs).adj := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (s.cross_correct a b).trans (ih (s.cross a b))

theorem crossMany_vertex_count [DecidableEq X] [DecidableEq B] (s : State X B) (a : X) (bs : List B) :
    Nat.card (s.crossMany a bs).Vertex=Nat.card s.Vertex+40*bs.length := by
  induction bs generalizing s with
  | nil => simp [crossMany]
  | cons b bs ih =>
    change Nat.card ((s.cross a b).crossMany a bs).Vertex=_
    rw [ih,cross_vertex_count,List.length_cons]
    omega

def retire {n : Nat} (s : State (Fin (n + 1)) B) : State (Fin n) (Option B) where
  Vertex := s.Vertex
  finite := s.finite
  adj := s.adj
  registry := s.registry.retire

end State

inductive Program : Nat → Type → Type 1 where
  | done {B : Type} : Program 0 B
  | insert {n : Nat} {B : Type} (crossings : List B)
      (rest : Program n (Option B)) : Program (n+1) B

namespace Program

def length : {n : Nat} → {B : Type} → Program n B → Nat
  | _, _, .done => 0
  | _, _, .insert bs rest => bs.length+rest.length

def run : {n : Nat} → {B : Type} → [DecidableEq B] →
    Program n B → State (Fin n) B → FiniteGraph
  | _, _, _, .done, s => s.toFiniteGraph
  | _, _, _, .insert bs rest, s => run rest ((s.crossMany 0 bs).retire)

theorem run_correct {n : Nat} {B : Type} (p : Program n B) :
    ∀ [DecidableEq B] (s : State (Fin n) B),
    PathCover.Hamiltonian s.adj ↔ PathCover.Hamiltonian (p.run s).adj := by
  induction p with
  | done => intro inst s; rfl
  | insert bs rest ih =>
    intro inst s
    exact (s.crossMany_correct 0 bs).trans (ih ((s.crossMany 0 bs).retire))

theorem run_vertex_count {n : Nat} {B : Type} (p : Program n B) :
    ∀ [DecidableEq B] (s : State (Fin n) B),
    Nat.card (p.run s).Vertex=Nat.card s.Vertex+40*p.length := by
  induction p with
  | done => intro inst s; simp [run,length]
  | insert bs rest ih =>
    intro inst s
    change Nat.card (rest.run ((s.crossMany 0 bs).retire)).Vertex=_
    rw [ih]
    change Nat.card (s.crossMany 0 bs).Vertex+40*rest.length=_
    rw [State.crossMany_vertex_count]
    simp only [length]
    omega

/-- A formula-independent label trace of the graph operations. `pending` names
unprocessed lines, and `old` names the already inserted bundles. -/
def trace : {n : Nat} → {B : Type} → Program n B → (Fin n → Nat) → (B → Nat) → List (Nat×Nat)
  | _, _, .done, _, _ => []
  | _, _, .insert bs rest, pending, old =>
      bs.map (fun b => (old b,pending 0)) ++
        rest.trace (fun i => pending i.succ) (fun b => Option.elim b (pending 0) old)

theorem trace_length {n : Nat} {B : Type} (p : Program n B)
    : ∀ (pending : Fin n → Nat) (old : B → Nat), (p.trace pending old).length=p.length := by
  induction p with
  | done => intro pending old; rfl
  | insert bs rest ih =>
    intro pending old
    simp only [trace,List.length_append,List.length_map,length]
    rw [ih]

end Program
end GridHardness.XorLineRegistry
