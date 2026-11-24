/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrthogonalTentacle
public import GridHardness.CycleToPath
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Orthogonal Tentacle Return

Return routes and Hamiltonian cycles in the same concrete orthogonal
strip chains as `OrthogonalTentacle.build`.
-/

public section

namespace GridHardness.OrthogonalTentacle
open CliffordSynthesis SimpleGraph SimpleGraph.Walk
set_option backward.isDefEq.respectTransparency false

/-- Replace a traversed edge by a path whose only old vertices are its ends. -/
theorem replace_route_subwalk {S T : Finset Point} {s t a b : Point}
    (p : lattice.Walk s t) (hp : p.IsPath) (hpc : ∀ v, v ∈ p.support ↔ v ∈ S)
    (hab : lattice.Adj a b) (he : hab.toWalk.IsSubwalk p)
    (hq : HasRoute T a b) (hinter : S ∩ T = {a, b}) : HasRoute (S ∪ T) s t := by
  obtain ⟨q, hq, hqc⟩ := hq
  obtain ⟨l, r, rfl⟩ := he
  have hqn : ¬ q.Nil := by intro hn; exact hab.ne (Walk.Nil.eq hn)
  let L := l.support.dropLast
  let M := q.dropLast.support.tail
  let R := r.support.tail
  have hqs : (a :: M) ++ [b] = q.support := by
    rw [show a :: M = q.dropLast.support from q.dropLast.cons_tail_support]
    exact q.support_dropLast_concat hqn
  have hps : ((l.append hab.toWalk).append r).support = L ++ a :: b :: R := by
    rw [← Walk.append_assoc, Walk.support_append_eq_support_dropLast_append]
    simp only [Adj.toWalk, Walk.cons_append, Walk.nil_append, Walk.support_cons]
    rw [← r.cons_tail_support]
  have hnew : ((l.append q).append r).support = L ++ a :: (M ++ b :: R) := by
    rw [← Walk.append_assoc, Walk.support_append_eq_support_dropLast_append,
      Walk.support_append_eq_support_dropLast_append, ← hqs]
    simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    rw [← r.cons_tail_support]
    simp [L, R, List.append_assoc]
  have hroute := q.isChain_adj_support
  rw [← hqs] at hroute
  have hold := ((l.append hab.toWalk).append r).isChain_adj_support
  rw [hps] at hold
  have hnod := hp.support_nodup
  rw [hps] at hnod
  have hqnod := hq.support_nodup
  rw [← hqs] at hqnod
  obtain ⟨_, hn, hm⟩ := insert_route_order lattice.Adj L M R a b hold hroute hnod hqnod
    (by
      intro v hv hv'
      have hs : v ∈ S := (hpc v).mp (hps.symm ▸ hv)
      have ht : v ∈ T := (hqc v).mp (hqs ▸ hv')
      have hi : v ∈ S ∩ T := Finset.mem_inter.mpr ⟨hs, ht⟩
      simpa [hinter] using hi)
  refine ⟨(l.append q).append r, ?_, ?_⟩
  · rw [Walk.isPath_def, hnew]
    exact hn
  · intro v
    rw [hnew, hm, ← hps, hqs, hpc, hqc, Finset.mem_union]

/-- Either orientation of an undirected traversed edge can be replaced. -/
theorem replace_route_edge {S T : Finset Point} {s t a b : Point}
    (p : lattice.Walk s t) (hp : p.IsPath) (hpc : ∀ v, v ∈ p.support ↔ v ∈ S)
    (he : p.toSubgraph.Adj a b) (hq : HasRoute T a b)
    (hinter : S ∩ T = {a, b}) : HasRoute (S ∪ T) s t := by
  have hab : lattice.Adj a b := he.adj_sub
  have hedge := Walk.adj_toSubgraph_iff_mem_edges.mp he
  rcases (Walk.isSubwalk_toWalk_iff_mem_edges hab).mpr hedge with h | h
  · exact replace_route_subwalk p hp hpc hab h hq hinter
  · obtain ⟨q, hq, hqc⟩ := hq
    have hrev : HasRoute T b a := ⟨q.reverse, hq.reverse, by simpa using hqc⟩
    exact replace_route_subwalk p hp hpc hab.symm h hrev (by rw [hinter, Finset.pair_comm])

/-- Every route uses each of the two available neighbours of an internal vertex. -/
theorem route_forced_neighbor {S : Finset Point} {s t a b x : Point}
    (p : lattice.Walk s t) (hp : p.IsPath) (hc : ∀ v, v ∈ p.support ↔ v ∈ S)
    (hb : b ∈ S) (hs : s ≠ b) (ht : t ≠ b)
    (hx : ∀ v ∈ S, lattice.Adj b v → v = a ∨ v = x) : p.toSubgraph.Adj b a := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp ((hc b).mpr hb)
  have hi0 : i ≠ 0 := by
    intro h; subst i
    simp only [Walk.getVert_zero] at hi
    exact hs hi
  have hil' : i < p.length := by
    by_contra h
    have hie : i = p.length := by omega
    subst i
    simp only [Walk.getVert_length] at hi
    exact ht hi
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
  rcases hu with hu | hu
  · have h := (p.toSubgraph_adj_getVert (by omega : i - 1 < p.length)).symm
    have he : i - 1 + 1 = i := by omega
    simpa [he, hi, hu] using h
  · rcases hv with hv | hv
    · simpa [hi, hv] using p.toSubgraph_adj_getVert hil'
    · exact False.elim (hne (hu.trans hv.symm))

theorem rect_far_return (horizontal : Bool) (origin : Point) (n : Nat) :
    HasRoute (rect horizontal origin n) (far horizontal origin n 0) (far horizontal origin n 1) := by
  have hpar : TentacleStrip.parity (TentacleStrip.corner n 1 0) ≠
      TentacleStrip.parity (TentacleStrip.corner n 1 1) := by
    simp only [TentacleStrip.parity, TentacleStrip.corner, Nat.one_ne_zero, ite_false,
      Fin.val_last, Fin.val_zero, Fin.val_one]
    omega
  obtain ⟨p, hp⟩ := (TentacleStrip.corner_route_iff n 1 1 0 1).mpr hpar
  simpa [far, TentacleStrip.corner, TentacleStrip.point] using lift_strip_route horizontal origin n hp

theorem rect_near_neighbors (horizontal : Bool) (origin : Point) (n : Nat)
    {p : Point} (hp : p ∈ rect horizontal origin n)
    (ha : lattice.Adj (place horizontal origin (0, 0)) p) :
    p = place horizontal origin (1, 0) ∨ p = place horizontal origin (0, 1) := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
  change IntegerGrid.manhattan _ _ = 1 at ha
  rw [place_distance, manhattan_one_iff] at ha
  simp only [TentacleStrip.point, Prod.mk.injEq] at ha
  rcases v with ⟨i, r⟩
  fin_cases r
  all_goals simp only [Fin.val_zero, Fin.val_one] at ha
  · left; apply congrArg (place horizontal origin); apply Prod.ext <;> dsimp [TentacleStrip.point] <;> omega
  · right; apply congrArg (place horizontal origin); apply Prod.ext <;> dsimp [TentacleStrip.point] <;> omega

/-- Inserting the previous tentacle into the first side edge of a rectangle
constructs the next return route. No route condition is required of the new
geometry: its rectangle boundary route is proved above. -/
theorem append_strip_return (st : State) (hr : Ready st)
    (ht : TerminalPair st.points (tip st 0) (tip st 1)) (n : Nat) (hn : 3 ≤ n)
    (hold : HasRoute st.points (tip st 0) (tip st 1)) :
    HasRoute (st.extend n).points (tip (st.extend n) 0) (tip (st.extend n) 1) := by
  obtain ⟨p, hp, hc⟩ := rect_far_return st.horizontal st.origin n
  have hs0 : far st.horizontal st.origin n 0 ≠ place st.horizontal st.origin (0, 0) := by
    intro he
    have := place_injective st.horizontal st.origin he
    simp only [far] at he
    have := congrArg Prod.fst (place_injective st.horizontal st.origin he)
    simp only [Prod.fst] at this
    omega
  have hs1 : far st.horizontal st.origin n 1 ≠ place st.horizontal st.origin (0, 0) := by
    intro he
    have := congrArg Prod.fst (place_injective st.horizontal st.origin he)
    simp only [Prod.fst] at this
    omega
  have he : p.toSubgraph.Adj (tip st 0) (tip st 1) := by
    exact route_forced_neighbor p hp hc (near_mem_rect st.horizontal st.origin n 0) hs0 hs1
      (fun v hv ha => rect_near_neighbors st.horizontal st.origin n hv ha)
  have hi : rect st.horizontal st.origin n ∩ st.points = {tip st 0, tip st 1} := by
    rw [Finset.inter_comm]
    exact ready_intersection st hr ht n (by omega)
  have hh := replace_route_edge p hp hc he hold hi
  rw [tip_extend, tip_extend]
  simpa only [State.extend, Finset.union_comm] using hh

theorem base_return : HasRoute base.points (tip base 0) (tip base 1) := by
  simpa [base, tip, place, far] using rect_far_return true (0, 0) 3

/-- Return routes exist on the terminal rung of every constructed strip chain. -/
theorem build_terminal_return (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    HasRoute (build ns).points (tip (build ns) 0) (tip (build ns) 1) := by
  induction ns with
  | nil => exact base_return
  | cons n ns ih =>
    have hn' : ∀ m ∈ ns, 3 ≤ m := fun m hm => hn m (List.mem_cons_of_mem n hm)
    have hg := build_geometry ns hn'
    exact append_strip_return (build ns) hg.1 hg.2.1 n (hn n (by simp)) (ih hn')

theorem build_base_mem (ns : List Nat) {p : Point} (hp : p ∈ base.points) :
    p ∈ (build ns).points := by
  induction ns with
  | nil => exact hp
  | cons n ns ih => exact Finset.mem_union_left _ ih

theorem build_start_neighbors (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) {p : Point}
    (hp : p ∈ (build ns).points) (ha : lattice.Adj (start 0) p) :
    p = start 1 ∨ p = (1, 0) := by
  induction ns with
  | nil =>
    have hi := (mem_rect_iff true (0, 0) 3 p).mp hp
    change IntegerGrid.manhattan _ _ = 1 at ha
    rw [manhattan_one_iff] at ha
    rcases p with ⟨x, y⟩
    simp only [InRect, ite_true, start, Fin.val_zero, Fin.val_one, Prod.mk.injEq] at hi ha ⊢
    omega
  | cons n ns ih =>
    have hn' : ∀ m ∈ ns, 3 ≤ m := fun m hm => hn m (List.mem_cons_of_mem n hm)
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ih hn' hp
    · have ho := (build_geometry ns hn').2.2
      have hi := (mem_rect_iff (build ns).horizontal (build ns).origin n p).mp hp
      have hx : 3 ≤ p.1 := by
        unfold InRect at hi
        split_ifs at hi <;> omega
      change IntegerGrid.manhattan _ _ = 1 at ha
      rw [manhattan_one_iff] at ha
      rcases p with ⟨x, y⟩
      simp only [start, Fin.val_zero, Prod.mk.injEq] at ha
      omega

/-- The starting corner keeps exactly its two neighbours throughout all bends. -/
theorem build_start_degree (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    letI : DecidableRel (finiteGrid (build ns).points).Adj := Classical.decRel _
    (finiteGrid (build ns).points).degree ⟨start 0, build_start_mem ns 0⟩ = 2 := by
  classical
  let a : (build ns).points := ⟨start 1, build_start_mem ns 1⟩
  let b : (build ns).points := ⟨(1, 0), build_base_mem ns (by
    exact point_mem_rect true (0, 0) 3 1 (by omega) 0)⟩
  have hab : a ≠ b := by intro he; have := congrArg Subtype.val he; simp [a, b, start] at this
  have hneigh : (finiteGrid (build ns).points).neighborFinset
      ⟨start 0, build_start_mem ns 0⟩ = {a, b} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ha
      rcases build_start_neighbors ns hn v.property ha with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · change IntegerGrid.manhattan (start 0) (start 1) = 1
        simp [start, IntegerGrid.manhattan]
      · change IntegerGrid.manhattan (start 0) (1, 0) = 1
        simp [start, IntegerGrid.manhattan]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneigh]
  simp [hab]

/-- Closing the terminal return route constructs a Hamiltonian cycle of the
actual finite induced grid on the constructed staircase. -/
theorem build_hamiltonian_cycle (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    ∃ a : (build ns).points, ∃ p : (finiteGrid (build ns).points).Walk a a,
      p.IsHamiltonianCycle := by
  obtain ⟨p, hp⟩ := (hasRoute_iff_hamiltonian (build_tip_mem ns hn 0)
    (build_tip_mem ns hn 1)).mp (build_terminal_return ns hn)
  have ha : (finiteGrid (build ns).points).Adj
      ⟨tip (build ns) 1, build_tip_mem ns hn 1⟩
      ⟨tip (build ns) 0, build_tip_mem ns hn 0⟩ := (build_geometry ns hn).2.1.2.2.1.symm
  refine ⟨_, Walk.cons ha p, ?_, ?_⟩
  · apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa using hp.isPath
    · have hl := hp.length_eq
      have hc := build_card ns hn
      simp only [Fintype.card_coe] at hl
      simp only [Walk.length_cons]
      omega
  · intro v
    simpa only [Walk.tail_cons, Walk.support_copy] using hp v

/-- Return routing at the initial rung, obtained by opening its forced edge
in the constructed Hamiltonian cycle. -/
theorem build_start_return_hamiltonian (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    ∃ p : (finiteGrid (build ns).points).Walk
      ⟨start 0, build_start_mem ns 0⟩ ⟨start 1, build_start_mem ns 1⟩,
      p.IsHamiltonian := by
  classical
  apply (cycle_iff_path_of_degree_two ?_ (build_start_degree ns hn) ?_).mp
    (build_hamiltonian_cycle ns hn)
  · simp only [Fintype.card_coe]
    rw [build_card ns hn]
    omega
  · change IntegerGrid.manhattan (start 0) (start 1) = 1
    simp [start, IntegerGrid.manhattan]

theorem build_start_return (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    HasRoute (build ns).points (start 0) (start 1) :=
  (hasRoute_iff_hamiltonian (build_start_mem ns 0) (build_start_mem ns 1)).mpr
    (build_start_return_hamiltonian ns hn)

/-- Both terminal-rung endpoints also have a genuine finite-grid return route. -/
theorem build_terminal_return_hamiltonian (ns : List Nat) (hn : ∀ n ∈ ns, 3 ≤ n) :
    ∃ p : (finiteGrid (build ns).points).Walk
      ⟨tip (build ns) 0, build_tip_mem ns hn 0⟩
      ⟨tip (build ns) 1, build_tip_mem ns hn 1⟩, p.IsHamiltonian :=
  (hasRoute_iff_hamiltonian (build_tip_mem ns hn 0) (build_tip_mem ns hn 1)).mp
    (build_terminal_return ns hn)

end GridHardness.OrthogonalTentacle
