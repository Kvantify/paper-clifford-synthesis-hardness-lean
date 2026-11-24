/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleFrame

/-!
# Signed Tentacle

Signed orthogonal strip chains. Validity consists solely of decidable
finite geometric conditions: lengths, endpoint alignment, exact overlap,
and exclusion of extra edges between disjoint strip interiors.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

def Aligned (a b : Fin 2 → Point) : Prop :=
  (a 0 = b 0 ∧ a 1 = b 1) ∨ (a 0 = b 1 ∧ a 1 = b 0)

instance (a b : Fin 2 → Point) : Decidable (Aligned a b) := by unfold Aligned; infer_instance

theorem Aligned.terminal {S : Finset Point} {a b : Fin 2 → Point} (ha : Aligned a b)
    (ht : TerminalPair S (a 0) (a 1)) : TerminalPair S (b 0) (b 1) := by
  rcases ha with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simpa [h0, h1] using ht
  · simpa [h0, h1] using ht.symm

theorem Aligned.range {a b : Fin 2 → Point} (ha : Aligned a b) (r : Fin 2) :
    ∃ t : Fin 2, a t = b r := by
  rcases ha with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> fin_cases r
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩
  · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

/-- No lattice edge joins the two disjoint interiors. All quantifiers are
bounded by the explicitly constructed finite point sets. -/
def Separated (S T : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ T, lattice.Adj p q → p ∈ T ∨ q ∈ S

instance (S T : Finset Point) : Decidable (Separated S T) := by
  unfold Separated
  infer_instance

theorem Separated.symm {S T : Finset Point} (h : Separated S T) : Separated T S := by
  intro p hp q hq ha
  exact (h q hq p hp ha.symm).symm

theorem terminal_union {S T : Finset Point} {a b : Point} (ht : TerminalPair S a b)
    (ha : a ∉ T) (hb : b ∉ T) (hsep : Separated S T) : TerminalPair (S ∪ T) a b := by
  refine ⟨Finset.mem_union_left _ ht.1, Finset.mem_union_left _ ht.2.1, ht.2.2.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := ht.2.2.2.1
    refine ⟨x, ?_⟩
    intro v hv hadj
    apply hx v ?_ hadj
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hv
    · exact (hsep a ht.1 v hv hadj).resolve_left ha
  · obtain ⟨x, hx⟩ := ht.2.2.2.2
    refine ⟨x, ?_⟩
    intro v hv hadj
    apply hx v ?_ hadj
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hv
    · exact (hsep b ht.2.1 v hv hadj).resolve_left hb

theorem strip_join_adj (f : Frame) : lattice.Adj (join f 0) (join f 1) :=
  f.hom.map_adj (by change IntegerGrid.manhattan (0, 0) (1, 0) = 1; decide)

theorem strip_join_neighbors (f : Frame) (n : Nat) {p : Point} (hp : p ∈ strip f n)
    (ha : lattice.Adj (join f 0) p) : p = join f 1 ∨ p = near f 1 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have ha' : lattice.Adj (place true (0, 0) (0, 0)) q := by
    change IntegerGrid.manhattan _ _ = 1 at ha ⊢
    rw [join, Frame.distance] at ha
    simpa [place] using ha
  have hh := rect_near_neighbors true (0, 0) n hq ha'
  simpa [place, join, near] using hh.imp (congrArg f.map) (congrArg f.map)

/-- The constructive cross-route step in an arbitrary signed frame. -/
theorem attach_cross {S : Finset Point} {s : Point} (f : Frame) (n : Nat) (hn : 1 ≤ n)
    (ht : TerminalPair S (join f 0) (join f 1)) (hs : ∀ r, s ≠ join f r)
    (hi : S ∩ strip f n = {join f 0, join f 1})
    (hr : ∀ r, color s ≠ color (join f r) → HasRoute S s (join f r))
    (t : Fin 2) (hc : color s ≠ color (far f n t)) :
    HasRoute (S ∪ strip f n) s (far f n t) := by
  have h01 := adjacent_color_ne (strip_join_adj f)
  have h0 := color_bounds (join f 0)
  have h1 := color_bounds (join f 1)
  have hss := color_bounds s
  by_cases h : color s ≠ color (join f 0)
  · have he : color s = color (join f 1) := by omega
    exact glue_terminal_route ht (hs 1) hi (hr 0 h)
      (strip_join_cross f n hn 1 t (by rwa [← he]))
  · have he : color s = color (join f 0) := by omega
    exact glue_terminal_route ht.symm (hs 0) (by rw [hi, Finset.pair_comm])
      (hr 1 (by omega)) (strip_join_cross f n hn 0 t (by rwa [← he]))

/-- Replace the new rectangle's joining edge by the old return route. -/
theorem attach_return {S : Finset Point} (f : Frame) (n : Nat) (hn : 2 ≤ n)
    (hi : S ∩ strip f n = {join f 0, join f 1})
    (hr : HasRoute S (join f 0) (join f 1)) :
    HasRoute (S ∪ strip f n) (far f n 0) (far f n 1) := by
  obtain ⟨p, hp, hc⟩ := strip_far_return f n
  have he : p.toSubgraph.Adj (join f 0) (join f 1) :=
    route_forced_neighbor p hp hc (join_mem f n (by omega) 0)
      (far_join_ne f n hn 0 0) (far_join_ne f n hn 1 0)
      (fun _ hv ha => strip_join_neighbors f n hv ha)
  have h := replace_route_edge p hp hc he hr (by rw [Finset.inter_comm, hi])
  simpa only [Finset.union_comm] using h

inductive Drawing where
  | base (frame : Frame) (length : Nat)
  | attach (old : Drawing) (frame : Frame) (length : Nat)
  deriving DecidableEq

def Drawing.points : Drawing → Finset Point
  | .base f n => strip f n
  | .attach d f n => d.points ∪ strip f n

def Drawing.start : Drawing → Fin 2 → Point
  | .base f _ => near f
  | .attach d _ _ => d.start

def Drawing.tip : Drawing → Fin 2 → Point
  | .base f n => far f n
  | .attach _ f n => far f n

def Drawing.Valid : Drawing → Prop
  | .base _ n => 3 ≤ n
  | .attach d f n => d.Valid ∧ 3 ≤ n ∧ Aligned d.tip (join f) ∧
      d.points ∩ strip f n = {join f 0, join f 1} ∧ Separated d.points (strip f n)

instance drawingValidDecidable : (d : Drawing) → Decidable d.Valid
  | .base _ n => inferInstanceAs (Decidable (3 ≤ n))
  | .attach d f n => by
    letI := drawingValidDecidable d
    unfold Drawing.Valid
    infer_instance

theorem far_not_mem_old {S : Finset Point} (f : Frame) (n : Nat) (hn : 2 ≤ n)
    (hi : S ∩ strip f n = {join f 0, join f 1}) (r : Fin 2) : far f n r ∉ S := by
  intro hp
  have hm : far f n r ∈ S ∩ strip f n := Finset.mem_inter.mpr ⟨hp, far_mem f n r⟩
  rw [hi, Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.elim (far_join_ne f n hn r 0) (far_join_ne f n hn r 1)

/-- Both boundary rungs retain degree at most two and remain disjoint. -/
theorem Drawing.geometry (d : Drawing) (hv : d.Valid) :
    TerminalPair d.points (d.start 0) (d.start 1) ∧
    TerminalPair d.points (d.tip 0) (d.tip 1) ∧ ∀ r t, d.start r ≠ d.tip t := by
  induction d with
  | base f n =>
    have hn : 3 ≤ n := hv
    exact ⟨strip_near_terminal f n, strip_far_terminal f n (by omega),
      fun r t => (far_near_ne f n (by omega) t r).symm⟩
  | attach d f n ih =>
    obtain ⟨hd, hn, hal, hi, hsep⟩ := hv
    obtain ⟨hs, ht, hdist⟩ := ih hd
    have hs_mem (r : Fin 2) : d.start r ∈ d.points := by
      fin_cases r
      · exact hs.1
      · exact hs.2.1
    have hs_not (r : Fin 2) : d.start r ∉ strip f n := by
      intro hp
      have hm : d.start r ∈ d.points ∩ strip f n := Finset.mem_inter.mpr ⟨hs_mem r, hp⟩
      rw [hi, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with he | he
      · obtain ⟨t, ht'⟩ := hal.range 0
        exact hdist r t (he.trans ht'.symm)
      · obtain ⟨t, ht'⟩ := hal.range 1
        exact hdist r t (he.trans ht'.symm)
    refine ⟨terminal_union hs (hs_not 0) (hs_not 1) hsep, ?_, ?_⟩
    · have h := terminal_union (strip_far_terminal f n (by omega))
        (far_not_mem_old f n (by omega) hi 0) (far_not_mem_old f n (by omega) hi 1) hsep.symm
      simpa only [Drawing.points, Drawing.tip, Finset.union_comm] using h
    · intro r t he
      change d.start r = far f n t at he
      exact far_not_mem_old f n (by omega) hi t (he ▸ hs_mem r)

theorem Drawing.start_mem (d : Drawing) (hv : d.Valid) (r : Fin 2) : d.start r ∈ d.points := by
  have h := (d.geometry hv).1
  fin_cases r
  · exact h.1
  · exact h.2.1

theorem Drawing.tip_mem (d : Drawing) (hv : d.Valid) (r : Fin 2) : d.tip r ∈ d.points := by
  have h := (d.geometry hv).2.1
  fin_cases r
  · exact h.1
  · exact h.2.1

/-- Cross routes follow from geometry for every finite list of signed turns. -/
theorem Drawing.cross (d : Drawing) (hv : d.Valid) (r t : Fin 2)
    (hc : color (d.start r) ≠ color (d.tip t)) : HasRoute d.points (d.start r) (d.tip t) := by
  induction d generalizing r t with
  | base f n => exact strip_cross f n r t hc
  | attach d f n ih =>
    obtain ⟨hd, hn, hal, hi, hsep⟩ := hv
    obtain ⟨_, ht, hdist⟩ := d.geometry hd
    apply attach_cross f n (by omega) (hal.terminal ht) ?_ hi ?_ t hc
    · intro j
      obtain ⟨k, hk⟩ := hal.range j
      rw [← hk]
      exact hdist r k
    · intro j hcolor
      obtain ⟨k, hk⟩ := hal.range j
      rw [← hk] at hcolor ⊢
      exact ih hd r k hcolor

/-- Return routing at the terminal rung of the same geometric construction. -/
theorem Drawing.terminal_return (d : Drawing) (hv : d.Valid) :
    HasRoute d.points (d.tip 0) (d.tip 1) := by
  induction d with
  | base f n => exact strip_far_return f n
  | attach d f n ih =>
    obtain ⟨hd, hn, hal, hi, _⟩ := hv
    apply attach_return f n (by omega) hi
    have hr := ih hd
    rcases hal with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hr
    · obtain ⟨p, hp, hc⟩ := hr
      have hr' : HasRoute d.points (d.tip 1) (d.tip 0) :=
        ⟨p.reverse, hp.reverse, by simpa only [Walk.support_reverse, List.mem_reverse] using hc⟩
      simpa only [h0, h1] using hr'

/-- Half the exact number of lattice vertices. Each bend contributes its
strip length, since the joining rung already belongs to the old drawing. -/
def Drawing.halfSize : Drawing → Nat
  | .base _ n => n + 1
  | .attach d _ n => d.halfSize + n

theorem Drawing.card (d : Drawing) (hv : d.Valid) : d.points.card = 2 * d.halfSize := by
  induction d with
  | base f n => exact strip_card f n
  | attach d f n ih =>
    obtain ⟨hd, _, _, hi, _⟩ := hv
    have h := Finset.card_union_add_card_inter d.points (strip f n)
    rw [hi, Finset.card_pair (join_ne f), strip_card, ih hd] at h
    change (d.points ∪ strip f n).card = 2 * (d.halfSize + n)
    omega

theorem Drawing.card_ge_eight (d : Drawing) (hv : d.Valid) : 8 ≤ d.points.card := by
  rw [d.card hv]
  have hs : 4 ≤ d.halfSize := by
    induction d with
    | base f n => change 3 ≤ n at hv; change 4 ≤ n + 1; omega
    | attach d f n ih => have hh := ih hv.1; change 4 ≤ d.halfSize + n; omega
  omega

theorem Drawing.cross_iff (d : Drawing) (hv : d.Valid) (r t : Fin 2) :
    HasRoute d.points (d.start r) (d.tip t) ↔ color (d.start r) ≠ color (d.tip t) := by
  constructor
  · intro h
    exact route_opposite_color h ⟨d.halfSize, by rw [d.card hv]; omega⟩
  · exact d.cross hv r t

/-- The endpoint parity characterization in the actual finite induced grid. -/
theorem Drawing.hamiltonian_iff (d : Drawing) (hv : d.Valid) (r t : Fin 2) :
    (∃ p : (finiteGrid d.points).Walk ⟨d.start r, d.start_mem hv r⟩
      ⟨d.tip t, d.tip_mem hv t⟩, p.IsHamiltonian) ↔
        color (d.start r) ≠ color (d.tip t) := by
  rw [← hasRoute_iff_hamiltonian]
  exact d.cross_iff hv r t

theorem Drawing.terminal_return_hamiltonian (d : Drawing) (hv : d.Valid) :
    ∃ p : (finiteGrid d.points).Walk ⟨d.tip 0, d.tip_mem hv 0⟩
      ⟨d.tip 1, d.tip_mem hv 1⟩, p.IsHamiltonian :=
  (hasRoute_iff_hamiltonian (d.tip_mem hv 0) (d.tip_mem hv 1)).mp (d.terminal_return hv)

/-- The boundary return route closes to a spanning cycle of the induced grid. -/
theorem Drawing.hamiltonian_cycle (d : Drawing) (hv : d.Valid) :
    ∃ a : d.points, ∃ p : (finiteGrid d.points).Walk a a, p.IsHamiltonianCycle := by
  obtain ⟨p, hp⟩ := d.terminal_return_hamiltonian hv
  have ha : (finiteGrid d.points).Adj ⟨d.tip 1, d.tip_mem hv 1⟩
      ⟨d.tip 0, d.tip_mem hv 0⟩ := (d.geometry hv).2.1.2.2.1.symm
  refine ⟨_, Walk.cons ha p, ?_, ?_⟩
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa using hp.isPath
    · have hl := hp.length_eq
      have hc := d.card_ge_eight hv
      simp only [Fintype.card_coe] at hl
      simp only [Walk.length_cons]
      omega
  · intro v
    simpa only [Walk.tail_cons, Walk.support_copy] using hp v

def Drawing.startNext : Drawing → Point
  | .base f _ => f.map (1, 0)
  | .attach d _ _ => d.startNext

theorem Drawing.startNext_properties (d : Drawing) (hv : d.Valid) :
    d.startNext ∈ d.points ∧ lattice.Adj (d.start 0) d.startNext ∧ d.start 1 ≠ d.startNext := by
  induction d with
  | base f n =>
    have hn : 3 ≤ n := hv
    refine ⟨join_mem f n (by omega) 1, strip_join_adj f, ?_⟩
    intro he
    have hh := f.injective he
    simp at hh
  | attach d f n ih =>
    obtain ⟨hm, ha, hn⟩ := ih hv.1
    exact ⟨Finset.mem_union_left _ hm, ha, hn⟩

/-- The geometric two-neighbour condition gives exact degree two when the
second neighbour is present; the proof explicitly identifies the finite
neighbour set. -/
theorem terminal_degree {S : Finset Point} {a b c : Point} (ht : TerminalPair S a b)
    (hc : c ∈ S) (ha : lattice.Adj a c) (hbc : b ≠ c) :
    letI : DecidableRel (finiteGrid S).Adj := Classical.decRel _
    (finiteGrid S).degree ⟨a, ht.1⟩ = 2 := by
  classical
  obtain ⟨x, hx⟩ := ht.2.2.2.1
  have he : c = x := (hx c hc ha).resolve_left hbc.symm
  let b' : S := ⟨b, ht.2.1⟩
  let c' : S := ⟨c, hc⟩
  have hn : b' ≠ c' := fun h => hbc (congrArg Subtype.val h)
  have hset : (finiteGrid S).neighborFinset ⟨a, ht.1⟩ = {b', c'} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv
      rcases hx v.val v.property hv with hv | hv
      · exact Or.inl (Subtype.ext hv)
      · exact Or.inr (Subtype.ext (hv.trans he.symm))
    · rintro (rfl | rfl)
      · exact ht.2.2.1
      · exact ha
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hset]
  simp [hn]

theorem Drawing.start_return_hamiltonian (d : Drawing) (hv : d.Valid) :
    ∃ p : (finiteGrid d.points).Walk ⟨d.start 0, d.start_mem hv 0⟩
      ⟨d.start 1, d.start_mem hv 1⟩, p.IsHamiltonian := by
  classical
  obtain ⟨hm, ha, hn⟩ := d.startNext_properties hv
  have ht := (d.geometry hv).1
  have hd : (finiteGrid d.points).degree ⟨d.start 0, d.start_mem hv 0⟩ = 2 :=
    terminal_degree ht hm ha hn
  have hab : (finiteGrid d.points).Adj ⟨d.start 0, d.start_mem hv 0⟩
      ⟨d.start 1, d.start_mem hv 1⟩ := ht.2.2.1
  apply (cycle_iff_path_of_degree_two ?_ hd hab).mp (d.hamiltonian_cycle hv)
  simp only [Fintype.card_coe]
  exact (by omega : 3 ≤ 8).trans (d.card_ge_eight hv)

theorem Drawing.start_return (d : Drawing) (hv : d.Valid) :
    HasRoute d.points (d.start 0) (d.start 1) :=
  (hasRoute_iff_hamiltonian (d.start_mem hv 0) (d.start_mem hv 1)).mpr
    (d.start_return_hamiltonian hv)

def Drawing.corner (d : Drawing) (side row : Fin 2) : Point :=
  if side = 0 then d.start row else d.tip row

theorem Drawing.corner_mem (d : Drawing) (hv : d.Valid) (side row : Fin 2) :
    d.corner side row ∈ d.points := by
  unfold Drawing.corner
  split_ifs
  · exact d.start_mem hv row
  · exact d.tip_mem hv row

theorem route_reverse {S : Finset Point} {a b : Point} (h : HasRoute S a b) : HasRoute S b a := by
  obtain ⟨p, hp, hc⟩ := h
  exact ⟨p.reverse, hp.reverse, by simpa only [Walk.support_reverse, List.mem_reverse] using hc⟩

/-- All four tentacle corners, including both same-side return pairings,
have the complete checkerboard-parity characterization. -/
theorem Drawing.corner_route_iff (d : Drawing) (hv : d.Valid) (a b r t : Fin 2) :
    HasRoute d.points (d.corner a r) (d.corner b t) ↔
      color (d.corner a r) ≠ color (d.corner b t) := by
  constructor
  · intro h
    exact route_opposite_color h ⟨d.halfSize, by rw [d.card hv]; omega⟩
  · intro hc
    fin_cases a <;> fin_cases b <;> simp [Drawing.corner] at hc ⊢
    · fin_cases r <;> fin_cases t
      · exact False.elim (hc rfl)
      · exact d.start_return hv
      · exact route_reverse (d.start_return hv)
      · exact False.elim (hc rfl)
    · exact d.cross hv r t hc
    · exact route_reverse (d.cross hv t r (fun h => hc h.symm))
    · fin_cases r <;> fin_cases t
      · exact False.elim (hc rfl)
      · exact d.terminal_return hv
      · exact route_reverse (d.terminal_return hv)
      · exact False.elim (hc rfl)

theorem Drawing.corner_hamiltonian_iff (d : Drawing) (hv : d.Valid) (a b r t : Fin 2) :
    (∃ p : (finiteGrid d.points).Walk ⟨d.corner a r, d.corner_mem hv a r⟩
      ⟨d.corner b t, d.corner_mem hv b t⟩, p.IsHamiltonian) ↔
        color (d.corner a r) ≠ color (d.corner b t) := by
  rw [← hasRoute_iff_hamiltonian]
  exact d.corner_route_iff hv a b r t

end GridHardness.SignedTentacle
