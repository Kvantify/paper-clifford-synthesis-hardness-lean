/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.NineCluster
public import GridHardness.SignedTentacle

/-!
# Nine Cluster Attachment

Concrete cluster docks for the grid construction in [ItaiPapadimitriouSzwarcfiter1982]. Even-side docks
have two boundary edges along one reserved cluster edge; odd-side docks
have one edge at the corresponding corner. The return insertion theorem
uses the actual signed tentacle and the actual induced-grid cluster.
-/

@[expose] public section

namespace GridHardness.NineClusterAttachment
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

def points : Finset Point := Finset.univ.image NineCluster.point

def corner (s : Fin 4) : Point := NineCluster.point (NineCluster.port s)
def mateIndex : Fin 4 → Fin 9 := ![3, 1, 5, 7]
def mate (s : Fin 4) : Point := NineCluster.point (mateIndex s)

/-- Left, bottom, right, and top docking frames. At an even cluster the
second lane faces its reserved edge; at an odd cluster it faces away. -/
def dock (twoEdges : Bool) : Fin 4 → Frame :=
  ![⟨true, true, !twoEdges, (-1, 0)⟩,
    ⟨false, true, twoEdges, (2, -1)⟩,
    ⟨true, false, twoEdges, (3, 2)⟩,
    ⟨false, false, !twoEdges, (0, 3)⟩]

theorem mem_points_iff (p : Point) : p ∈ points ↔
    0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 2 := by
  have he : points = (Finset.Icc (0 : Int) 2).product (Finset.Icc (0 : Int) 2) := by decide
  rw [he]
  rcases p with ⟨x, y⟩
  exact (Finset.mem_product.trans (and_congr Finset.mem_Icc Finset.mem_Icc)).trans and_assoc

theorem corner_mem (s : Fin 4) : corner s ∈ points :=
  Finset.mem_image.mpr ⟨NineCluster.port s, Finset.mem_univ _, rfl⟩

theorem mate_mem (s : Fin 4) : mate s ∈ points :=
  Finset.mem_image.mpr ⟨mateIndex s, Finset.mem_univ _, rfl⟩

theorem corner_ne_mate : ∀ s, corner s ≠ mate s := by decide

theorem dock_disjoint (twoEdges : Bool) (s : Fin 4) (n : Nat) :
    Disjoint points (strip (dock twoEdges s) n) := by
  apply Finset.disjoint_left.mpr
  intro p hp ht
  have hc := (mem_points_iff p).mp hp
  have hm := (mem_strip_iff (dock twoEdges s) n p).mp ht
  rcases p with ⟨x, y⟩
  fin_cases s <;> cases twoEdges <;>
    simp [dock, Frame.unmap, sign] at hm <;> dsimp at hc <;> omega

/-- Exact induced-grid interface: there are precisely two available
cluster–strip edges on the even side and one on the odd side. -/
theorem dock_boundary (twoEdges : Bool) (s : Fin 4) (n : Nat) {c t : Point}
    (hc : c ∈ points) (ht : t ∈ strip (dock twoEdges s) n) :
    lattice.Adj c t ↔
      (c = corner s ∧ t = near (dock twoEdges s) 0) ∨
      (twoEdges = true ∧ c = mate s ∧ t = near (dock twoEdges s) 1) := by
  have hc' := (mem_points_iff c).mp hc
  have ht' := (mem_strip_iff (dock twoEdges s) n t).mp ht
  change IntegerGrid.manhattan c t = 1 ↔ _
  rw [manhattan_one_iff]
  rcases c with ⟨x, y⟩
  rcases t with ⟨u, v⟩
  fin_cases s <;> cases twoEdges <;>
    simp [dock, Frame.unmap, Frame.map, sign, place, near, corner, mate, mateIndex,
      NineCluster.port, NineCluster.point, Prod.mk.injEq] at ht' ⊢ <;> dsimp at hc' <;> omega

theorem dock_first_adjacent (twoEdges : Bool) (s : Fin 4) :
    lattice.Adj (corner s) (near (dock twoEdges s) 0) := by
  apply (dock_boundary twoEdges s 0 (corner_mem s) (near_mem _ _ _)).mpr
  exact Or.inl ⟨rfl, rfl⟩

theorem dock_second_adjacent (s : Fin 4) :
    lattice.Adj (mate s) (near (dock true s) 1) := by
  apply (dock_boundary true s 0 (mate_mem s) (near_mem _ _ _)).mpr
  exact Or.inr ⟨rfl, rfl, rfl⟩

def clusterEmbedding : NineCluster.graph →g lattice where
  toFun := NineCluster.point
  map_rel' := by intro u v h; exact h

theorem source_cluster_route (i j : Fin 4) (hij : i ≠ j) :
    ∃ p : NineCluster.graph.Walk (NineCluster.port i) (NineCluster.port j),
      p.IsHamiltonian ∧ ∀ e ∈ NineCluster.markedEdges, e ∈ p.edges := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact NineCluster.nine_cluster_route i j h
  · obtain ⟨p, hp, he⟩ := NineCluster.nine_cluster_route j i h
    refine ⟨p.reverse, ?_, ?_⟩
    · intro v
      simpa only [Walk.support_reverse, List.count_reverse] using hp v
    · intro e hm
      simpa only [Walk.edges_reverse, List.mem_reverse] using he e hm

/-- Cluster paths join any two distinct corner ports and traverse each
reserved edge, expressed in the common ambient integer lattice. -/
theorem cluster_route (i j : Fin 4) (hij : i ≠ j) :
    ∃ p : lattice.Walk (corner i) (corner j), p.IsPath ∧
      (∀ v, v ∈ p.support ↔ v ∈ points) ∧
      ∀ s, p.toSubgraph.Adj (corner s) (mate s) := by
  obtain ⟨p, hp, he⟩ := source_cluster_route i j hij
  refine ⟨p.map clusterEmbedding, hp.isPath.map NineCluster.point_injective, ?_, ?_⟩
  · intro v
    simp only [Walk.support_map, List.mem_map, points, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, _, hw⟩
      exact ⟨w, hw⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, hp.mem_support w, hw⟩
  · intro s
    have hm : s(NineCluster.port s, mateIndex s) ∈ NineCluster.markedEdges := by
      fin_cases s <;> decide
    rw [Walk.adj_toSubgraph_iff_mem_edges, Walk.edges_map]
    exact List.mem_map.mpr ⟨_, he _ hm, rfl⟩

/-- Added strips must remain disjoint and nonadjacent to the cluster. -/
def Clear (S : Finset Point) : Prop :=
  Disjoint points S ∧ ∀ c ∈ points, ∀ t ∈ S, ¬lattice.Adj c t

/-- A geometric docking certificate: the first strip uses the fixed dock;
all later signed strips remain clear of the cluster. Validity of the
strip chain itself is the separate `Drawing.Valid` condition. -/
def Docked (twoEdges : Bool) (side : Fin 4) : Drawing → Prop
  | .base f _ => f = dock twoEdges side
  | .attach d f n => Docked twoEdges side d ∧ Clear (strip f n)

instance (S : Finset Point) : Decidable (Clear S) := by unfold Clear; infer_instance

instance dockedDecidable (b : Bool) (s : Fin 4) : (d : Drawing) → Decidable (Docked b s d)
  | .base f _ => inferInstanceAs (Decidable (f = dock b s))
  | .attach d f n => by
    letI := dockedDecidable b s d
    unfold Docked
    infer_instance

theorem Docked.starts {b : Bool} {s : Fin 4} {d : Drawing} (h : Docked b s d) (r : Fin 2) :
    d.start r = near (dock b s) r := by
  induction d with
  | base f n => change f = dock b s at h; subst f; rfl
  | attach d f n ih => exact ih h.1

theorem Docked.disjoint {b : Bool} {s : Fin 4} {d : Drawing} (h : Docked b s d) :
    Disjoint points d.points := by
  induction d with
  | base f n => change f = dock b s at h; subst f; exact dock_disjoint b s n
  | attach d f n ih => exact Finset.disjoint_union_right.mpr ⟨ih h.1, h.2.1⟩

/-- The exact one- or two-edge interface persists through arbitrary valid
signed bends once their concrete strips stay clear of the cluster. -/
theorem Docked.boundary {b : Bool} {s : Fin 4} {d : Drawing} (h : Docked b s d)
    {c t : Point} (hc : c ∈ points) (ht : t ∈ d.points) :
    lattice.Adj c t ↔ (c = corner s ∧ t = d.start 0) ∨
      (b = true ∧ c = mate s ∧ t = d.start 1) := by
  constructor
  · intro ha
    induction d with
    | base f n =>
      change f = dock b s at h
      subst f
      exact (dock_boundary b s n hc ht).mp ha
    | attach d f n ih =>
      rcases Finset.mem_union.mp ht with ht | ht
      · exact ih h.1 ht
      · exact False.elim (h.2.2 c hc t ht ha)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · rw [h.starts]
      exact dock_first_adjacent b s
    · rw [h.starts]
      exact dock_second_adjacent s

/-- Add the two cluster endpoint vertices to an isolated return route. -/
theorem surround_route {S : Finset Point} {s t a b : Point} (h : HasRoute S s t)
    (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b)
    (hleft : lattice.Adj a s) (hright : lattice.Adj t b) :
    HasRoute (S ∪ {a, b}) a b := by
  obtain ⟨p, hp, hc⟩ := h
  have ha' : a ∉ p.support := fun hm => ha ((hc a).mp hm)
  have hb' : b ∉ p.support := fun hm => hb ((hc b).mp hm)
  refine ⟨(Walk.cons hleft p).concat hright, ?_, ?_⟩
  · rw [Walk.isPath_def, Walk.support_concat, Walk.support_cons]
    simp [List.nodup_append, hp.support_nodup, ha', hab]
    intro x y hm he
    exact hb' (he ▸ hm)
  · intro v
    simp only [Walk.support_concat, Walk.support_cons, List.mem_append, List.mem_cons,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hc]
    tauto

/-- Absorb one unused even-side tentacle into a reserved cluster edge.
The corner-to-corner route still spans every cluster and tentacle vertex. -/
theorem cluster_with_return_route (d : Drawing) (hv : d.Valid) (s i j : Fin 4)
    (hd : Docked true s d) (hij : i ≠ j) :
    HasRoute (points ∪ d.points) (corner i) (corner j) := by
  obtain ⟨p, hp, hc, he⟩ := cluster_route i j hij
  have hca := corner_mem s
  have hcb := mate_mem s
  have hdis := Finset.disjoint_left.mp hd.disjoint
  have ha : corner s ∉ d.points := hdis hca
  have hb : mate s ∉ d.points := hdis hcb
  have hr : HasRoute (d.points ∪ {corner s, mate s}) (corner s) (mate s) :=
    surround_route (d.start_return hv) ha hb (corner_ne_mate s)
      (by rw [hd.starts]; exact dock_first_adjacent true s)
      (by rw [hd.starts]; exact (dock_second_adjacent s).symm)
  have hi : points ∩ (d.points ∪ {corner s, mate s}) = {corner s, mate s} := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hc', ht | he'⟩
      · exact False.elim (hdis hc' ht)
      · exact he'
    · rintro (rfl | rfl)
      · exact ⟨hca, Or.inr (Or.inl rfl)⟩
      · exact ⟨hcb, Or.inr (Or.inr rfl)⟩
  have hh := replace_route_edge p hp hc (he s) hr hi
  have hu : points ∪ (d.points ∪ {corner s, mate s}) = points ∪ d.points := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · subst v; exact Or.inl hca
      · subst v; exact Or.inl hcb
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rwa [hu] at hh

/-- The return-insertion result on the actual finite induced-grid graph. -/
theorem cluster_with_return_hamiltonian (d : Drawing) (hv : d.Valid) (s i j : Fin 4)
    (hd : Docked true s d) (hij : i ≠ j) :
    ∃ p : (finiteGrid (points ∪ d.points)).Walk
      ⟨corner i, Finset.mem_union_left _ (corner_mem i)⟩
      ⟨corner j, Finset.mem_union_left _ (corner_mem j)⟩, p.IsHamiltonian :=
  (hasRoute_iff_hamiltonian _ _).mp (cluster_with_return_route d hv s i j hd hij)

/-- A completely explicit infinite family of docked cluster assemblies. -/
theorem straight_cluster_return_hamiltonian (n : Nat) (hn : 3 ≤ n) (s i j : Fin 4)
    (hij : i ≠ j) :
    ∃ p : (finiteGrid (points ∪ strip (dock true s) n)).Walk
      ⟨corner i, Finset.mem_union_left _ (corner_mem i)⟩
      ⟨corner j, Finset.mem_union_left _ (corner_mem j)⟩, p.IsHamiltonian :=
  cluster_with_return_hamiltonian (.base (dock true s) n) hn s i j rfl hij

/-- All actual lattice edges from the cluster into an attached drawing. -/
def boundaryEdges (d : Drawing) : Finset (Point × Point) :=
  (points.product d.points).filter (fun e => lattice.Adj e.1 e.2)

theorem Docked.boundary_edges {b : Bool} {s : Fin 4} {d : Drawing}
    (h : Docked b s d) (hv : d.Valid) :
    boundaryEdges d = if b then {(corner s, d.start 0), (mate s, d.start 1)}
      else {(corner s, d.start 0)} := by
  ext e
  rcases e with ⟨c, t⟩
  simp only [boundaryEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hm, ha⟩
    have hm' := Finset.mem_product.mp hm
    have hh := (h.boundary hm'.1 hm'.2).mp ha
    cases b <;> simpa only [ite_true, Bool.false_eq_true, ite_false, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, false_and, or_false, true_and] using hh
  · intro he
    cases b
    · have hh : c = corner s ∧ t = d.start 0 := by simpa using he
      rcases hh with ⟨rfl, rfl⟩
      refine ⟨Finset.mem_product.mpr ⟨corner_mem s, d.start_mem hv 0⟩, ?_⟩
      rw [h.starts]
      exact dock_first_adjacent false s
    · have hh : (c = corner s ∧ t = d.start 0) ∨ (c = mate s ∧ t = d.start 1) := by
        simpa using he
      rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨Finset.mem_product.mpr ⟨corner_mem s, d.start_mem hv 0⟩, ?_⟩
        rw [h.starts]
        exact dock_first_adjacent true s
      · refine ⟨Finset.mem_product.mpr ⟨mate_mem s, d.start_mem hv 1⟩, ?_⟩
        rw [h.starts]
        exact dock_second_adjacent s

/-- Exactly two available cut edges at an even-side dock, and exactly one
at an odd-side dock, for the full bent tentacle rather than only its stub. -/
theorem Docked.boundary_card {b : Bool} {s : Fin 4} {d : Drawing}
    (h : Docked b s d) (hv : d.Valid) : (boundaryEdges d).card = if b then 2 else 1 := by
  rw [h.boundary_edges hv]
  have hn : (corner s, d.start 0) ≠ (mate s, d.start 1) :=
    fun he => corner_ne_mate s (congrArg Prod.fst he)
  cases b <;> simp [hn]

end GridHardness.NineClusterAttachment
