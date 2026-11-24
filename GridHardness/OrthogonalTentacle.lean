/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TentacleGluing

/-!
# Orthogonal Tentacle

Cross routing through nonbranching orthogonal strips.  Routes are first
constructed in the ambient lattice with an exact finite support, then
restricted to the induced finite graph.
-/

@[expose] public section

namespace GridHardness.OrthogonalTentacle
open CliffordSynthesis SimpleGraph SimpleGraph.Walk
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int

def lattice : SimpleGraph Point where
  Adj p q := IntegerGrid.manhattan p q = 1
  symm := ⟨by intro p q h; rwa [IntegerGrid.manhattan_comm]⟩
  loopless := ⟨by intro p; simp [IntegerGrid.manhattan]⟩

def HasRoute (S : Finset Point) (a b : Point) : Prop :=
  ∃ p : lattice.Walk a b, p.IsPath ∧ ∀ v, v ∈ p.support ↔ v ∈ S

def color (p : Point) : Int := (p.1 + p.2) % 2

theorem color_bounds (p : Point) : 0 ≤ color p ∧ color p < 2 := by
  unfold color
  omega

theorem adjacent_color_ne {p q : Point} (h : lattice.Adj p q) : color p ≠ color q := by
  change IntegerGrid.manhattan p q = 1 at h
  rw [manhattan_one_iff] at h
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [Prod.mk.injEq] at h
  unfold color
  dsimp at *
  omega

/-- Translation, optionally exchanging the two coordinate axes. -/
def place (horizontal : Bool) (origin p : Point) : Point :=
  if horizontal then (origin.1 + p.1, origin.2 + p.2)
  else (origin.1 + p.2, origin.2 + p.1)

theorem place_injective (horizontal : Bool) (origin : Point) :
    Function.Injective (place horizontal origin) := by
  intro p q h
  cases horizontal <;> simp only [place, Bool.false_eq_true, ite_false, ite_true, Prod.mk.injEq] at h
  all_goals exact Prod.ext (by omega) (by omega)

theorem place_distance (horizontal : Bool) (origin p q : Point) :
    IntegerGrid.manhattan (place horizontal origin p) (place horizontal origin q) =
      IntegerGrid.manhattan p q := by
  cases horizontal <;> simp [place, IntegerGrid.manhattan, Nat.add_comm]

theorem place_color_eq_iff (horizontal : Bool) (origin p q : Point) :
    color (place horizontal origin p) = color (place horizontal origin q) ↔ color p = color q := by
  cases horizontal <;> simp only [place, Bool.false_eq_true, ite_false, ite_true, color] <;> omega

def rect (horizontal : Bool) (origin : Point) (n : Nat) : Finset Point :=
  Finset.univ.image (fun v : TentacleStrip.Vertex n => place horizontal origin (TentacleStrip.point v))

def InRect (horizontal : Bool) (origin : Point) (n : Nat) (p : Point) : Prop :=
  if horizontal then
    origin.1 ≤ p.1 ∧ p.1 ≤ origin.1 + (n : Int) ∧ origin.2 ≤ p.2 ∧ p.2 ≤ origin.2 + 1
  else origin.1 ≤ p.1 ∧ p.1 ≤ origin.1 + 1 ∧ origin.2 ≤ p.2 ∧ p.2 ≤ origin.2 + (n : Int)

theorem mem_rect_iff (horizontal : Bool) (origin : Point) (n : Nat) (p : Point) :
    p ∈ rect horizontal origin n ↔ InRect horizontal origin n p := by
  constructor
  · rintro hp
    obtain ⟨⟨i, row⟩, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := i.is_lt
    have hr := row.is_lt
    cases horizontal <;> dsimp [InRect, place, TentacleStrip.point] <;> omega
  · intro hp
    rw [rect, Finset.mem_image]
    cases horizontal
    · refine ⟨(⟨(p.2 - origin.2).toNat, ?_⟩, ⟨(p.1 - origin.1).toNat, ?_⟩), Finset.mem_univ _, ?_⟩
      · dsimp [InRect] at hp; omega
      · dsimp [InRect] at hp; omega
      · apply Prod.ext <;> dsimp [place, TentacleStrip.point, InRect] at hp ⊢ <;> omega
    · refine ⟨(⟨(p.1 - origin.1).toNat, ?_⟩, ⟨(p.2 - origin.2).toNat, ?_⟩), Finset.mem_univ _, ?_⟩
      · dsimp [InRect] at hp; omega
      · dsimp [InRect] at hp; omega
      · apply Prod.ext <;> dsimp [place, TentacleStrip.point, InRect] at hp ⊢ <;> omega

def far (horizontal : Bool) (origin : Point) (n : Nat) (row : Fin 2) : Point :=
  place horizontal origin ((n : Int), (row.val : Int))

def stripEmbedding (horizontal : Bool) (origin : Point) (n : Nat) :
    TentacleStrip.graph n →g lattice where
  toFun := fun v => place horizontal origin (TentacleStrip.point v)
  map_rel' := by
    intro v w h
    change IntegerGrid.manhattan _ _ = 1
    rw [place_distance]
    exact h

theorem lift_strip_route (horizontal : Bool) (origin : Point) (n : Nat)
    {a b : TentacleStrip.Vertex n} {p : (TentacleStrip.graph n).Walk a b}
    (hp : p.IsHamiltonian) :
    HasRoute (rect horizontal origin n) (place horizontal origin (TentacleStrip.point a))
      (place horizontal origin (TentacleStrip.point b)) := by
  let f := stripEmbedding horizontal origin n
  have hf : Function.Injective f :=
    (place_injective horizontal origin).comp (TentacleStrip.point_injective n)
  refine ⟨p.map f, hp.isPath.map hf, ?_⟩
  intro v
  simp only [Walk.support_map, List.mem_map, rect, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hp.mem_support w, hw⟩

theorem rect_corner_cross (horizontal : Bool) (origin : Point) (n : Nat) (row : Fin 2)
    (hc : color (place horizontal origin (0, 0)) ≠ color (far horizontal origin n row)) :
    HasRoute (rect horizontal origin n) (place horizontal origin (0, 0))
      (far horizontal origin n row) := by
  have hc' : color (0, 0) ≠ color ((n : Int), (row.val : Int)) := by
    exact fun h => hc ((place_color_eq_iff _ _ _ _).mpr h)
  have hpar : (0 + n + row.val) % 2 = 1 := by
    unfold color at hc'
    dsimp at hc'
    omega
  obtain ⟨p, hp⟩ := TentacleStrip.cross_route_between n 0 row hpar
  exact lift_strip_route horizontal origin n hp

theorem rect_offset_cross (horizontal : Bool) (origin : Point) (n : Nat) (hn : 1 ≤ n)
    (row : Fin 2)
    (hc : color (place horizontal origin (1, 0)) ≠ color (far horizontal origin n row)) :
    HasRoute (rect horizontal origin n) (place horizontal origin (1, 0))
      (far horizontal origin n row) := by
  have hc' : color (1, 0) ≠ color ((n : Int), (row.val : Int)) := by
    exact fun h => hc ((place_color_eq_iff _ _ _ _).mpr h)
  have hrow : row.val = n % 2 := by
    unfold color at hc'
    dsimp at hc'
    omega
  obtain ⟨p, hp⟩ := TentacleStrip.offset_cross_route n hn
  have he : (⟨n % 2, by omega⟩ : Fin 2) = row := Fin.ext hrow.symm
  rw [← he]
  exact lift_strip_route horizontal origin n hp

theorem rect_cross_between (horizontal : Bool) (origin : Point) (n : Nat) (r t : Fin 2)
    (hc : color (place horizontal origin (0, (r.val : Int))) ≠ color (far horizontal origin n t)) :
    HasRoute (rect horizontal origin n) (place horizontal origin (0, (r.val : Int)))
      (far horizontal origin n t) := by
  have hc' : color (0, (r.val : Int)) ≠ color ((n : Int), (t.val : Int)) := by
    exact fun h => hc ((place_color_eq_iff _ _ _ _).mpr h)
  have hpar : (r.val + n + t.val) % 2 = 1 := by
    unfold color at hc'
    dsimp at hc'
    omega
  obtain ⟨p, hp⟩ := TentacleStrip.cross_route_between n r t hpar
  exact lift_strip_route horizontal origin n hp

/-- The two far corners have only their rung neighbour and one neighbour
back along the strip. This is a geometric condition, not a route premise. -/
def TerminalPair (S : Finset Point) (a b : Point) : Prop :=
  a ∈ S ∧ b ∈ S ∧ lattice.Adj a b ∧
    (∃ x, ∀ v ∈ S, lattice.Adj a v → v = b ∨ v = x) ∧
    (∃ y, ∀ v ∈ S, lattice.Adj b v → v = a ∨ v = y)

/-- An internal degree-two terminal forces the final edge of a simple route. -/
theorem terminal_penultimate {S : Finset Point} {s a b : Point}
    (ht : TerminalPair S a b) (hs : s ≠ b)
    (p : lattice.Walk s a) (hp : p.IsPath) (hc : ∀ v, v ∈ p.support ↔ v ∈ S) :
    p.penultimate = b := by
  obtain ⟨x, hx⟩ := ht.2.2.2.2
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp ((hc b).mpr ht.2.1)
  have hi0 : i ≠ 0 := by
    intro h; subst i
    simp only [Walk.getVert_zero] at hi
    exact hs hi
  have hil' : i < p.length := by
    by_contra h
    have hie : i = p.length := by omega
    subst i
    simp only [Walk.getVert_length] at hi
    exact ht.2.2.1.ne hi
  have hu := hx (p.getVert (i - 1)) ((hc _).mp (p.getVert_mem_support _))
    (by have h := (p.adj_getVert_succ (by omega : i - 1 < p.length)).symm
        have he : i - 1 + 1 = i := by omega
        simpa [he, hi] using h)
  have hv := hx (p.getVert (i + 1)) ((hc _).mp (p.getVert_mem_support _))
    (by simpa [hi] using p.adj_getVert_succ hil')
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro he
    have := hp.getVert_injOn (by change i - 1 ≤ p.length; omega)
      (by change i + 1 ≤ p.length; omega) he
    omega
  have hadj : p.toSubgraph.Adj b a := by
    rcases hu with hu | hu
    · have h := (p.toSubgraph_adj_getVert (by omega : i - 1 < p.length)).symm
      have he : i - 1 + 1 = i := by omega
      simpa [he, hi, hu] using h
    · rcases hv with hv | hv
      · simpa [hi, hv] using p.toSubgraph_adj_getVert hil'
      · exact False.elim (hne (hu.trans hv.symm))
  have hpn : ¬ p.Nil := by
    intro h
    have he := p.nil_iff_support_eq.mp h
    have hb := (hc b).mpr ht.2.1
    rw [he, List.mem_singleton] at hb
    exact hs hb.symm
  have hmem : b ∈ p.toSubgraph.neighborSet a := hadj.symm
  rw [hp.neighborSet_toSubgraph_endpoint hpn, Set.mem_singleton_iff] at hmem
  exact hmem.symm

theorem TerminalPair.symm {S : Finset Point} {a b : Point} (h : TerminalPair S a b) :
    TerminalPair S b a := ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.2, h.2.2.2.1⟩

theorem far_mem_rect (horizontal : Bool) (origin : Point) (n : Nat) (row : Fin 2) :
    far horizontal origin n row ∈ rect horizontal origin n := by
  exact Finset.mem_image.mpr ⟨(Fin.last n, row), Finset.mem_univ _, rfl⟩

theorem near_mem_rect (horizontal : Bool) (origin : Point) (n : Nat) (row : Fin 2) :
    place horizontal origin (0, (row.val : Int)) ∈ rect horizontal origin n := by
  exact Finset.mem_image.mpr ⟨(0, row), Finset.mem_univ _, rfl⟩

theorem far_adjacent (horizontal : Bool) (origin : Point) (n : Nat) :
    lattice.Adj (far horizontal origin n 0) (far horizontal origin n 1) := by
  change IntegerGrid.manhattan _ _ = 1
  rw [far, far, place_distance]
  simp [IntegerGrid.manhattan]

theorem far_neighbors (horizontal : Bool) (origin : Point) (n : Nat) (hn : 1 ≤ n)
    (row : Fin 2) {p : Point} (hp : p ∈ rect horizontal origin n)
    (ha : lattice.Adj (far horizontal origin n row) p) :
    p = far horizontal origin n row.rev ∨ p = place horizontal origin ((n : Int) - 1, (row.val : Int)) := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
  change IntegerGrid.manhattan _ _ = 1 at ha
  rw [far, place_distance, manhattan_one_iff] at ha
  simp only [TentacleStrip.point, Prod.mk.injEq] at ha
  have hv := v.1.is_lt
  obtain ⟨i, r⟩ := v
  fin_cases row <;> fin_cases r
  all_goals
    simp only [Fin.val_zero, Fin.val_one] at ha
    first
    | left; apply congrArg (place horizontal origin); apply Prod.ext <;> dsimp [TentacleStrip.point, far, Fin.rev] <;> omega
    | right; apply congrArg (place horizontal origin); apply Prod.ext <;> dsimp [TentacleStrip.point] <;> omega

theorem rect_terminal (horizontal : Bool) (origin : Point) (n : Nat) (hn : 1 ≤ n) :
    TerminalPair (rect horizontal origin n) (far horizontal origin n 0) (far horizontal origin n 1) := by
  refine ⟨far_mem_rect _ _ _ _, far_mem_rect _ _ _ _, far_adjacent _ _ _, ?_, ?_⟩
  · refine ⟨place horizontal origin ((n : Int) - 1, 0), ?_⟩
    intro v hv ha
    simpa using far_neighbors horizontal origin n hn 0 hv ha
  · refine ⟨place horizontal origin ((n : Int) - 1, 1), ?_⟩
    intro v hv ha
    simpa using far_neighbors horizontal origin n hn 1 hv ha

/-- A cross route follows the old terminal rung, then a route of the new
strip. Only the geometric two-point intersection is assumed. -/
theorem glue_terminal_route {S T : Finset Point} {s a b t : Point}
    (ht : TerminalPair S a b) (hs : s ≠ b)
    (hinter : S ∩ T = {a, b})
    (hp : HasRoute S s a) (hq : HasRoute T b t) : HasRoute (S ∪ T) s t := by
  obtain ⟨p, hp, hpc⟩ := hp
  obtain ⟨q, hq, hqc⟩ := hq
  have hend := terminal_penultimate ht hs p hp hpc
  let q' := q.copy hend.symm rfl
  have hq' : q'.IsPath := by simpa [q', Walk.isPath_def] using hq
  have hqc' : ∀ v, v ∈ q'.support ↔ v ∈ T := by simpa [q'] using hqc
  have haT : a ∈ T := by
    have h : a ∈ S ∩ T := by rw [hinter]; simp
    exact (Finset.mem_inter.mp h).2
  have hpn : ¬ p.Nil := by
    intro h
    have hb := (hpc b).mpr ht.2.1
    rw [p.nil_iff_support_eq.mp h, List.mem_singleton] at hb
    exact hs hb.symm
  have hinter' : ∀ v, v ∈ p.support → v ∈ q'.support → v = a ∨ v = p.penultimate := by
    intro v hv hv'
    have hm : v ∈ S ∩ T := Finset.mem_inter.mpr ⟨(hpc v).mp hv, (hqc' v).mp hv'⟩
    rw [hinter] at hm
    simpa [hend] using hm
  obtain ⟨hpath, hmem⟩ := splice_overlap_edge p hp hpn q' hq' ((hqc' a).mpr haT) hinter'
  refine ⟨p.dropLast.append q', hpath, ?_⟩
  intro v
  rw [hmem, hpc, hqc', Finset.mem_union]

/-- The complete turn step for cross routes, using corner or offset-corner
routing according to the checkerboard color of the old endpoint. -/
theorem append_strip_cross {S : Finset Point} {s : Point}
    (horizontal : Bool) (origin : Point) (n : Nat) (hn : 1 ≤ n)
    (ht : TerminalPair S (place horizontal origin (0, 0)) (place horizontal origin (1, 0)))
    (hs0 : s ≠ place horizontal origin (0, 0)) (hs1 : s ≠ place horizontal origin (1, 0))
    (hinter : S ∩ rect horizontal origin n =
      {place horizontal origin (0, 0), place horizontal origin (1, 0)})
    (hcross : ∀ t, t = place horizontal origin (0, 0) ∨ t = place horizontal origin (1, 0) →
      color s ≠ color t → HasRoute S s t)
    (row : Fin 2) (hc : color s ≠ color (far horizontal origin n row)) :
    HasRoute (S ∪ rect horizontal origin n) s (far horizontal origin n row) := by
  have h01 := adjacent_color_ne ht.2.2.1
  have hb0 := color_bounds (place horizontal origin (0, 0))
  have hb1 := color_bounds (place horizontal origin (1, 0))
  have hbs := color_bounds s
  by_cases h0 : color s ≠ color (place horizontal origin (0, 0))
  · have hscolor : color s = color (place horizontal origin (1, 0)) := by omega
    exact glue_terminal_route ht hs1 hinter (hcross _ (Or.inl rfl) h0)
      (rect_offset_cross horizontal origin n hn row (by rwa [← hscolor]))
  · have hscolor : color s = color (place horizontal origin (0, 0)) := by omega
    have h1 : color s ≠ color (place horizontal origin (1, 0)) := by omega
    have hinter' : S ∩ rect horizontal origin n =
        {place horizontal origin (1, 0), place horizontal origin (0, 0)} := by
      rw [hinter, Finset.pair_comm]
    exact glue_terminal_route ht.symm hs0 hinter' (hcross _ (Or.inr rfl) h1)
      (rect_corner_cross horizontal origin n row (by rwa [← hscolor]))

structure State where
  points : Finset Point
  horizontal : Bool
  origin : Point

def tip (st : State) (row : Fin 2) : Point :=
  place st.horizontal st.origin ((row.val : Int), 0)

def State.extend (st : State) (n : Nat) : State where
  points := st.points ∪ rect st.horizontal st.origin n
  horizontal := !st.horizontal
  origin := far st.horizontal st.origin n 0

def base : State := ⟨rect true (0, 0) 3, false, (3, 0)⟩

/-- A box ending at the two attachment vertices. Its long direction is the
new strip's transverse direction, so the next strip turns through 90°. -/
def Ready (st : State) : Prop :=
  ∀ p ∈ st.points, if st.horizontal then
    p.1 ≤ st.origin.1 + 1 ∧ p.2 ≤ st.origin.2
  else p.1 ≤ st.origin.1 ∧ p.2 ≤ st.origin.2 + 1

theorem tip_extend (st : State) (n : Nat) (row : Fin 2) :
    tip (st.extend n) row = far st.horizontal st.origin n row := by
  rcases st with ⟨S, h, o⟩
  cases h <;> simp [tip, State.extend, far, place]

theorem point_mem_rect (horizontal : Bool) (origin : Point) (n i : Nat) (hi : i ≤ n)
    (row : Fin 2) : place horizontal origin ((i : Int), (row.val : Int)) ∈ rect horizontal origin n := by
  exact Finset.mem_image.mpr ⟨(⟨i, by omega⟩, row), Finset.mem_univ _, rfl⟩

theorem ready_intersection (st : State) (hr : Ready st)
    (ht : TerminalPair st.points (tip st 0) (tip st 1)) (n : Nat) (hn : 1 ≤ n) :
    st.points ∩ rect st.horizontal st.origin n = {tip st 0, tip st 1} := by
  ext p
  rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hrect⟩
    have hbox := hr p hp
    obtain ⟨⟨i, row⟩, _, rfl⟩ := Finset.mem_image.mp hrect
    rcases st with ⟨S, h, o⟩
    cases h <;> dsimp [place, TentacleStrip.point] at hbox ⊢
    all_goals
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hrow : row.val = 0 := by omega
      rcases hi with hi | hi
      · left; apply Prod.ext <;> dsimp [tip, place] <;> omega
      · right; apply Prod.ext <;> dsimp [tip, place] <;> omega
  · rintro (rfl | rfl)
    · exact ⟨ht.1, point_mem_rect _ _ _ 0 (by omega) 0⟩
    · exact ⟨ht.2.1, point_mem_rect _ _ _ 1 hn 0⟩

/-- Besides the shared terminal edge, consecutive strips introduce no edge
between their disjoint interiors. This checks the induced-grid geometry,
not just a chosen subgraph of the lattice. -/
theorem ready_no_extra_edges (st : State) (hr : Ready st)
    (ht : TerminalPair st.points (tip st 0) (tip st 1)) (n : Nat)
    {p q : Point} (hp : p ∈ st.points) (hq : q ∈ rect st.horizontal st.origin n)
    (ha : lattice.Adj p q) : p ∈ rect st.horizontal st.origin n ∨ q ∈ st.points := by
  by_cases hp' : p ∈ rect st.horizontal st.origin n
  · exact Or.inl hp'
  · have hpbox := hr p hp
    have hqbox := (mem_rect_iff _ _ _ _).mp hq
    rw [mem_rect_iff] at hp'
    change IntegerGrid.manhattan p q = 1 at ha
    rw [manhattan_one_iff] at ha
    have hends : q = tip st 0 ∨ q = tip st 1 := by
      rcases st with ⟨S, hdir, o⟩
      rcases p with ⟨px, py⟩
      rcases q with ⟨qx, qy⟩
      cases hdir <;> simp only [InRect, tip, place, Bool.false_eq_true, ite_false,
        ite_true, Prod.mk.injEq] at hp' hpbox hqbox ha ⊢ <;> dsimp at * <;> omega
    exact Or.inr (hends.elim (fun h => h ▸ ht.1) (fun h => h ▸ ht.2.1))

theorem ready_extend (st : State) (hr : Ready st) (n : Nat) (hn : 1 ≤ n) : Ready (st.extend n) := by
  intro p hp
  change p ∈ st.points ∪ rect st.horizontal st.origin n at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have h := hr p hp
    rcases st with ⟨S, hdir, o⟩
    cases hdir <;> dsimp [State.extend, far, place] at * <;> omega
  · obtain ⟨⟨i, row⟩, _, rfl⟩ := Finset.mem_image.mp hp
    have hi := i.is_lt
    have hr := row.is_lt
    rcases st with ⟨S, hdir, o⟩
    cases hdir <;> dsimp [State.extend, far, place, TentacleStrip.point] at * <;> omega

theorem far_not_adjacent_old (st : State) (hr : Ready st) (n : Nat) (hn : 3 ≤ n)
    (row : Fin 2) {p : Point} (hp : p ∈ st.points) :
    ¬ lattice.Adj (far st.horizontal st.origin n row) p := by
  intro ha
  have h := hr p hp
  change IntegerGrid.manhattan _ _ = 1 at ha
  rw [manhattan_one_iff] at ha
  rcases st with ⟨S, hdir, o⟩
  rcases p with ⟨px, py⟩
  cases hdir <;> simp only [far, place, Bool.false_eq_true, ite_true, ite_false,
    Prod.mk.injEq] at ha h <;> dsimp at * <;> omega

theorem terminal_extend (st : State) (hr : Ready st) (n : Nat) (hn : 3 ≤ n) :
    TerminalPair (st.extend n).points (tip (st.extend n) 0) (tip (st.extend n) 1) := by
  rw [tip_extend, tip_extend]
  obtain ⟨ha, hb, hab, ⟨x, hx⟩, ⟨y, hy⟩⟩ := rect_terminal st.horizontal st.origin n (by omega)
  refine ⟨Finset.mem_union_right _ ha, Finset.mem_union_right _ hb, hab, ⟨x, ?_⟩, ⟨y, ?_⟩⟩
  · intro v hv hadj
    rcases Finset.mem_union.mp hv with hv | hv
    · exact False.elim (far_not_adjacent_old st hr n hn 0 hv hadj)
    · exact hx v hv hadj
  · intro v hv hadj
    rcases Finset.mem_union.mp hv with hv | hv
    · exact False.elim (far_not_adjacent_old st hr n hn 1 hv hadj)
    · exact hy v hv hadj

theorem origin_extend (st : State) (ho : 3 ≤ st.origin.1) (n : Nat) :
    3 ≤ (st.extend n).origin.1 := by
  rcases st with ⟨S, h, o⟩
  cases h <;> dsimp [State.extend, far, place] at * <;> omega

def start (row : Fin 2) : Point := (0, (row.val : Int))

theorem start_ne_tip (st : State) (ho : 3 ≤ st.origin.1) (r t : Fin 2) :
    start r ≠ tip st t := by
  intro he
  have hx := congrArg Prod.fst he
  rcases st with ⟨S, h, o⟩
  cases h <;> dsimp [start, tip, place] at * <;> omega

def CrossRoutes (st : State) : Prop :=
  ∀ r t : Fin 2, color (start r) ≠ color (tip st t) → HasRoute st.points (start r) (tip st t)

theorem cross_extend (st : State) (hr : Ready st)
    (ht : TerminalPair st.points (tip st 0) (tip st 1))
    (ho : 3 ≤ st.origin.1) (hc : CrossRoutes st) (n : Nat) (hn : 3 ≤ n) :
    CrossRoutes (st.extend n) := by
  intro r t hcolor
  rw [tip_extend] at hcolor ⊢
  apply append_strip_cross st.horizontal st.origin n (by omega) ht
    (start_ne_tip st ho r 0) (start_ne_tip st ho r 1)
    (ready_intersection st hr ht n (by omega)) ?_ t hcolor
  intro p hp hcp
  rcases hp with rfl | rfl
  · exact hc r 0 hcp
  · exact hc r 1 hcp

/-- Each list element is the length of one successive perpendicular strip.
The order is recursive from the tail; every step introduces one right-angle
bend and shares exactly the previous terminal edge. -/
def build : List Nat → State
  | [] => base
  | n :: ns => (build ns).extend n

theorem base_ready : Ready base := by
  intro p hp
  obtain ⟨⟨i, row⟩, _, rfl⟩ := Finset.mem_image.mp hp
  have hi := i.is_lt
  have hr := row.is_lt
  dsimp [base, place, TentacleStrip.point] at *
  omega

theorem base_terminal : TerminalPair base.points (tip base 0) (tip base 1) := by
  simpa [base, tip, far, place] using rect_terminal true (0, 0) 3 (by omega)

theorem base_cross : CrossRoutes base := by
  intro r t hc
  have h := rect_cross_between true (0, 0) 3 r t
  have hc' : color (place true (0, 0) (0, (r.val : Int))) ≠ color (far true (0, 0) 3 t) := by
    simpa [base, tip, far, place, start] using hc
  simpa [base, tip, far, place, start] using h hc'

theorem build_geometry (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    Ready (build ns) ∧ TerminalPair (build ns).points (tip (build ns) 0) (tip (build ns) 1) ∧
      3 ≤ (build ns).origin.1 := by
  induction ns with
  | nil => exact ⟨base_ready, base_terminal, by decide⟩
  | cons n ns ih =>
    have hnn := hn n (by simp)
    obtain ⟨hr, ht, ho⟩ := ih (fun m hm => hn m (by simp [hm]))
    exact ⟨ready_extend _ hr n (by omega), terminal_extend _ hr n hnn, origin_extend _ ho n⟩

/-- Cross Hamiltonian routes through a concrete orthogonal strip chain with
an arbitrary number of bends, for every opposite-color endpoint pair. -/
theorem build_cross (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) : CrossRoutes (build ns) := by
  induction ns with
  | nil => exact base_cross
  | cons n ns ih =>
    have hns : ∀ m ∈ ns, 3 ≤ m := fun m hm => hn m (by simp [hm])
    obtain ⟨hr, ht, ho⟩ := build_geometry ns hns
    exact cross_extend _ hr ht ho (ih hns) n (hn n (by simp))

theorem rect_card (horizontal : Bool) (origin : Point) (n : Nat) :
    (rect horizontal origin n).card = 2 * (n + 1) := by
  have hf : Function.Injective (fun v : TentacleStrip.Vertex n =>
      place horizontal origin (TentacleStrip.point v)) :=
    (place_injective horizontal origin).comp (TentacleStrip.point_injective n)
  rw [rect, Finset.card_image_of_injective _ hf]
  simp [TentacleStrip.Vertex, Nat.mul_comm]

theorem extend_card (st : State) (hr : Ready st)
    (ht : TerminalPair st.points (tip st 0) (tip st 1)) (n : Nat) (hn : 1 ≤ n) :
    (st.extend n).points.card = st.points.card + 2 * n := by
  have h := Finset.card_union_add_card_inter st.points (rect st.horizontal st.origin n)
  rw [ready_intersection st hr ht n hn, Finset.card_pair ht.2.2.1.ne, rect_card] at h
  change (st.points ∪ rect st.horizontal st.origin n).card = _
  omega

/-- Exact linear size in the sum of the strip lengths. -/
theorem build_card (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    (build ns).points.card = 8 + 2 * ns.sum := by
  induction ns with
  | nil => exact rect_card true (0, 0) 3
  | cons n ns ih =>
    have hns : ∀ m ∈ ns, 3 ≤ m := fun m hm => hn m (by simp [hm])
    have hnn := hn n (by simp)
    obtain ⟨hr, ht, _⟩ := build_geometry ns hns
    change ((build ns).extend n).points.card = _
    rw [extend_card _ hr ht n (by omega), ih hns, List.sum_cons]
    omega

theorem walk_color {a b : Point} (p : lattice.Walk a b) :
    (color a + (p.length : Int)) % 2 = color b := by
  induction p with
  | nil => simp [color]
  | @cons a b c h p ih =>
    have hn := adjacent_color_ne h
    have ha := color_bounds a
    have hb := color_bounds b
    simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

theorem route_opposite_color {S : Finset Point} {a b : Point}
    (h : HasRoute S a b) (heven : Even S.card) : color a ≠ color b := by
  obtain ⟨p, hp, hc⟩ := h
  have heq : p.support.toFinset = S := by ext v; simpa using hc v
  have hlen : p.support.length = S.card := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup, heq]
  have hlen' := p.length_support
  have hpar := walk_color p
  have ha := color_bounds a
  obtain ⟨k, hk⟩ := heven
  omega

theorem build_cross_iff (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) (r t : Fin 2) :
    HasRoute (build ns).points (start r) (tip (build ns) t) ↔
      color (start r) ≠ color (tip (build ns) t) := by
  constructor
  · intro h
    apply route_opposite_color h
    refine ⟨4 + ns.sum, ?_⟩
    rw [build_card ns hn]
    omega
  · exact build_cross ns hn r t

def finiteGrid (S : Finset Point) : SimpleGraph S := lattice.induce (S : Set Point)

/-- Exact finite-support routes are genuine Hamiltonian walks of the vertex-
induced finite grid; this is not merely a path predicate on an infinite graph. -/
theorem hasRoute_iff_hamiltonian {S : Finset Point} {a b : Point} (ha : a ∈ S) (hb : b ∈ S) :
    HasRoute S a b ↔ ∃ p : (finiteGrid S).Walk ⟨a, ha⟩ ⟨b, hb⟩, p.IsHamiltonian := by
  constructor
  · rintro ⟨p, hp, hc⟩
    have hsub : ∀ v ∈ p.support, v ∈ (S : Set Point) := fun v hv => (hc v).mp hv
    let q := p.induce (S : Set Point) hsub
    have hpath : q.IsPath := by
      apply Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce (S : Set Point)).toHom)
      dsimp [q]
      rw [Walk.map_induce]
      exact hp
    refine ⟨q, hpath.isHamiltonian_of_mem ?_⟩
    intro v
    dsimp [q]
    rw [Walk.support_induce]
    simpa using (hc v.val).mpr v.property
  · rintro ⟨p, hp⟩
    let f := (SimpleGraph.Embedding.induce (S : Set Point) (G := lattice)).toHom
    refine ⟨p.map f, hp.isPath.map Subtype.val_injective, ?_⟩
    intro v
    simp only [Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨w, _, hw⟩
      exact hw ▸ w.property
    · intro hv
      exact ⟨⟨v, hv⟩, hp.mem_support _, rfl⟩

theorem build_start_mem (ns : List Nat) (row : Fin 2) : start row ∈ (build ns).points := by
  induction ns with
  | nil => simpa [base, build, start, place] using near_mem_rect true (0, 0) 3 row
  | cons n ns ih => exact Finset.mem_union_left _ ih

theorem build_tip_mem (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) (row : Fin 2) :
    tip (build ns) row ∈ (build ns).points := by
  have ht := (build_geometry ns hn).2.1
  fin_cases row
  · exact ht.1
  · exact ht.2.1

/-- A complete endpoint characterization for the concrete arbitrary-bend
family, stated using mathlib's actual Hamiltonian-walk predicate. -/
theorem build_hamiltonian_iff (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) (r t : Fin 2) :
    (∃ p : (finiteGrid (build ns).points).Walk
      ⟨start r, build_start_mem ns r⟩ ⟨tip (build ns) t, build_tip_mem ns hn t⟩,
      p.IsHamiltonian) ↔ color (start r) ≠ color (tip (build ns) t) := by
  rw [← hasRoute_iff_hamiltonian]
  exact build_cross_iff ns hn r t

/-- No geometric assumptions remain for any number of length-three bends. -/
theorem repeated_bends_hamiltonian_iff (k : Nat) (r t : Fin 2) :
    (∃ p : (finiteGrid (build (List.replicate k 3)).points).Walk
      ⟨start r, build_start_mem _ r⟩
      ⟨tip (build (List.replicate k 3)) t,
        build_tip_mem _ (by intro n hn; simp only [List.mem_replicate] at hn; omega) t⟩,
      p.IsHamiltonian) ↔ color (start r) ≠ color (tip (build (List.replicate k 3)) t) :=
  build_hamiltonian_iff _ (by intro n hn; simp only [List.mem_replicate] at hn; omega) r t

end GridHardness.OrthogonalTentacle
