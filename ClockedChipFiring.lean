import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

/-!
# A counterexample to Jiang's subcycle-period conjecture

Section 5 of Tian-Yi Jiang, "On the Period Lengths of the Parallel Chip-Firing
Game", arXiv:1003.0943 (2010), proposes a divisor of one subcycle length or the
exact least common multiple of lengths of disjoint subcycles.

There are two rings (lengths 6 and 27) attached by bridges to one central
vertex. A 35-chip configuration has least return time 18. The cycle
classification below allows even the length-two return along an edge.
`not_jiang_cycle_conjecture` refutes the stated disjunction under this
permissive convention. Divisibility by an lcm is a different assertion
and holds for the specific witness, since 18 divides 54.

This file is standalone with mathlib. Verified with Lean 4.20.0 / mathlib v4.20.0.
-/

namespace ClockedChipFiring

abbrev Table (n : ℕ) := Fin n → List (Fin n)
abbrev Config (n : ℕ) := Fin n → ℕ

def Fires {n : ℕ} (G : Table n) (x : Config n) (v : Fin n) : Bool :=
  decide ((G v).length ≤ x v)

/-- All threshold comparisons refer to the same pre-tick state. -/
def step {n : ℕ} (G : Table n) (x : Config n) : Config n := fun v =>
  (x v - (if Fires G x v then (G v).length else 0)) + (G v).countP (Fires G x)

def after {n : ℕ} (G : Table n) (x : Config n) : ℕ → Config n
  | 0 => x
  | t + 1 => step G (after G x t)

def ExactPeriod {n : ℕ} (G : Table n) (x : Config n) (p : ℕ) : Prop :=
  0 < p ∧ after G x p = x ∧ ∀ t, 0 < t → t < p → after G x t ≠ x

def EventualPeriod {n : ℕ} (G : Table n) (x : Config n) (p : ℕ) : Prop :=
  ∃ t, ExactPeriod G (after G x t) p

inductive Reaches {n : ℕ} (G : Table n) : Fin n → Fin n → Prop
  | refl (u) : Reaches G u u
  | extend {u v w} : Reaches G u v → w ∈ G v → Reaches G u w

def IsSimpleConnected {n : ℕ} (G : Table n) : Prop :=
  (∀ v, (G v).Nodup) ∧ (∀ v, v ∉ G v) ∧
  (∀ u v, v ∈ G u ↔ u ∈ G v) ∧ (∀ u v, Reaches G u v)

def Closes {n : ℕ} (G : Table n) (start : Fin n) : Fin n → List (Fin n) → Prop
  | u, [] => start ∈ G u
  | u, v :: rest => v ∈ G u ∧ Closes G start v rest

/-- A closed path with no repeated listed vertex, recording its starting vertex
exactly once. A tail of length one admits the two-way traversal of one edge. -/
def IsSubcycle {n : ℕ} (G : Table n) : List (Fin n) → Prop
  | [] => False
  | s :: rest => rest ≠ [] ∧ (s :: rest).Nodup ∧ Closes G s s rest

def IsSimpleCycle {n : ℕ} (G : Table n) (c : List (Fin n)) : Prop :=
  IsSubcycle G c ∧ 3 ≤ c.length

def cycleLcm {n : ℕ} (cs : List (List (Fin n))) : ℕ :=
  (cs.map List.length).foldr Nat.lcm 1

def ExplainedBy {n : ℕ} (isCycle : List (Fin n) → Prop) (p : ℕ) : Prop :=
  (∃ c, isCycle c ∧ p ∣ c.length) ∨
  (∃ cs, (∀ c ∈ cs, isCycle c) ∧
    cs.Pairwise (fun a b => ∀ v ∈ a, v ∉ b) ∧ cycleLcm cs = p)

/-- `allowBacktracks = false` uses ordinary undirected simple cycles.
The true case even admits a length-two backtrack. -/
def JiangCycleConjecture (allowBacktracks : Bool) : Prop :=
  ∀ (n : ℕ) (G : Table n), IsSimpleConnected G →
  ∀ (x : Config n) (p : ℕ), EventualPeriod G x p →
    ExplainedBy (if allowBacktracks then IsSubcycle G else IsSimpleCycle G) p

section Search
variable {n : ℕ}

private def testClose (G : Table n) (s u : Fin n) (visited : List (Fin n))
    (allowed : ℕ → Bool) : Bool :=
  !(decide (s ∈ G u)) || allowed visited.length

/-- Exhaust the simple continuations of a partial path using only actual
neighbors. The list of visited vertices has its most recent vertex first. -/
private def scan (G : Table n) (s : Fin n) (allowed : ℕ → Bool) :
    ℕ → Fin n → List (Fin n) → Bool
  | 0, u, seen => testClose G s u seen allowed
  | d+1, u, seen => testClose G s u seen allowed &&
      (G u).all (fun v => decide (v ∈ seen) || scan G s allowed d v (v :: seen))

private theorem scan_sound (G : Table n) (s : Fin n) (allowed : ℕ → Bool)
    (d : ℕ) (u : Fin n) (seen tail : List (Fin n))
    (checked : scan G s allowed d u seen = true) (path : Closes G s u tail)
    (short : tail.length ≤ d) (nd : tail.Nodup)
    (fresh : ∀ x ∈ tail, x ∉ seen) : allowed (seen.length + tail.length) = true := by
  induction d generalizing u seen tail with
  | zero =>
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    have closingEdge : s ∈ G u := path
    simpa [scan, testClose, closingEdge] using checked
  | succ d ih =>
    obtain ⟨localCheck, children⟩ := Bool.and_eq_true_iff.mp checked
    cases tail with
    | nil =>
      have closingEdge : s ∈ G u := path
      simpa [testClose, closingEdge] using localCheck
    | cons v rest =>
      obtain ⟨edge, next⟩ := path
      have fv : v ∉ seen := fresh v (by simp)
      have child := (List.all_eq_true.mp children) v edge
      simp only [decide_eq_false fv, Bool.false_or] at child
      obtain ⟨distinct, nd'⟩ := List.nodup_cons.mp nd
      have fresh' : ∀ x ∈ rest, x ∉ v :: seen := by
        intro x hx h
        rcases List.mem_cons.mp h with eq | old
        · exact distinct (eq ▸ hx)
        · exact fresh x (List.mem_cons_of_mem v hx) old
      have bound : rest.length ≤ d := by simpa using short
      have result := ih v (v :: seen) rest child next bound nd' fresh'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

private theorem lengths_from_scan (G : Table n) (allowed : ℕ → Bool)
    (checked : ∀ s, scan G s allowed n s [s] = true) (c : List (Fin n))
    (cycle : IsSubcycle G c) : allowed c.length = true := by
  cases c with
  | nil => exact False.elim cycle
  | cons s tail =>
    obtain ⟨_, nd, walk⟩ := cycle
    obtain ⟨startFresh, restND⟩ := List.nodup_cons.mp nd
    have short : tail.length ≤ n := by simpa using restND.length_le_card
    have fresh : ∀ x ∈ tail, x ∉ [s] := by
      intro x hx h
      have eq : x = s := by simpa using h
      exact startFresh (eq ▸ hx)
    simpa [Nat.add_comm] using scan_sound G s allowed n s [s] tail (checked s)
      walk short restND fresh

end Search

/-! ## The finite graph and its 18-phase orbit -/

def graph : Fin 34 → List (Fin 34) := fun v =>
  match v.val with
  | 0 => [1, 5, 33]
  | 1 => [0, 2]
  | 2 => [1, 3]
  | 3 => [2, 4]
  | 4 => [3, 5]
  | 5 => [0, 4]
  | 6 => [7, 32, 33]
  | 7 => [6, 8]
  | 8 => [7, 9]
  | 9 => [8, 10]
  | 10 => [9, 11]
  | 11 => [10, 12]
  | 12 => [11, 13]
  | 13 => [12, 14]
  | 14 => [13, 15]
  | 15 => [14, 16]
  | 16 => [15, 17]
  | 17 => [16, 18]
  | 18 => [17, 19]
  | 19 => [18, 20]
  | 20 => [19, 21]
  | 21 => [20, 22]
  | 22 => [21, 23]
  | 23 => [22, 24]
  | 24 => [23, 25]
  | 25 => [24, 26]
  | 26 => [25, 27]
  | 27 => [26, 28]
  | 28 => [27, 29]
  | 29 => [28, 30]
  | 30 => [29, 31]
  | 31 => [30, 32]
  | 32 => [6, 31]
  | _ => [0, 6]

/-- The two ring labels are 0–5 and 6–32. The hub is 33. -/
def phaseRow : Fin 18 → List ℕ := fun v =>
  match v.val with
  | 0 => [3, 0, 2, 0, 1, 1, 3, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 0]
  | 1 => [0, 2, 0, 1, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 2]
  | 2 => [3, 0, 1, 1, 2, 0, 3, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 0]
  | 3 => [0, 1, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 2]
  | 4 => [2, 1, 2, 0, 2, 0, 2, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 0]
  | 5 => [2, 2, 0, 2, 0, 1, 2, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0]
  | 6 => [3, 0, 2, 0, 1, 1, 3, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 0]
  | 7 => [0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 2]
  | 8 => [3, 0, 1, 1, 2, 0, 2, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 0]
  | 9 => [0, 1, 1, 2, 0, 2, 3, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 1]
  | 10 => [1, 1, 2, 0, 2, 0, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 2]
  | 11 => [2, 2, 0, 2, 0, 1, 3, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 0]
  | 12 => [3, 0, 2, 0, 1, 1, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 1]
  | 13 => [0, 2, 0, 1, 1, 2, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 2]
  | 14 => [3, 0, 1, 1, 2, 0, 2, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0]
  | 15 => [0, 1, 1, 2, 0, 2, 3, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 1]
  | 16 => [1, 1, 2, 0, 2, 0, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 2]
  | _ => [2, 2, 0, 2, 0, 1, 2, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 1, 2, 0, 2, 0, 1, 1, 2, 0, 0]

/-- One path from the hub to each vertex, including both ends. -/
def hubPath : Fin 34 → List (Fin 34) := fun v =>
  match v.val with
  | 0 => [33, 0]
  | 1 => [33, 0, 1]
  | 2 => [33, 0, 1, 2]
  | 3 => [33, 0, 1, 2, 3]
  | 4 => [33, 0, 5, 4]
  | 5 => [33, 0, 5]
  | 6 => [33, 6]
  | 7 => [33, 6, 7]
  | 8 => [33, 6, 7, 8]
  | 9 => [33, 6, 7, 8, 9]
  | 10 => [33, 6, 7, 8, 9, 10]
  | 11 => [33, 6, 7, 8, 9, 10, 11]
  | 12 => [33, 6, 7, 8, 9, 10, 11, 12]
  | 13 => [33, 6, 7, 8, 9, 10, 11, 12, 13]
  | 14 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  | 15 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | 16 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
  | 17 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  | 18 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]
  | 19 => [33, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
  | 20 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20]
  | 21 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21]
  | 22 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22]
  | 23 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25, 24, 23]
  | 24 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25, 24]
  | 25 => [33, 6, 32, 31, 30, 29, 28, 27, 26, 25]
  | 26 => [33, 6, 32, 31, 30, 29, 28, 27, 26]
  | 27 => [33, 6, 32, 31, 30, 29, 28, 27]
  | 28 => [33, 6, 32, 31, 30, 29, 28]
  | 29 => [33, 6, 32, 31, 30, 29]
  | 30 => [33, 6, 32, 31, 30]
  | 31 => [33, 6, 32, 31]
  | 32 => [33, 6, 32]
  | _ => [33]

def trace (t : Fin 18) (v : Fin 34) : ℕ := (phaseRow t).getD v.val 0
def initial : Config 34 := trace 0

private def phase (t : ℕ) : Fin 18 := ⟨t % 18, Nat.mod_lt _ (by decide)⟩

/-- Every one of the 18 successor rows is derived from the chip-firing rule. -/
theorem step_trace (t : Fin 18) : step graph (trace t) = trace (phase (t.val+1)) := by
  funext v
  revert t v
  decide

theorem all_ticks (t : ℕ) : after graph initial t = trace (phase t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [after, ih, step_trace]
    apply congrArg trace
    apply Fin.ext
    simp [phase, Nat.add_mod]

private theorem early_disagreement :
    ∀ t : Fin 18, t ≠ 0 → ∃ v : Fin 34, trace t v ≠ initial v := by decide

theorem exact_period_eighteen : ExactPeriod graph initial 18 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [all_ticks]
    rfl
  · intro k pos short h
    let t : Fin 18 := ⟨k, short⟩
    have pt : phase k = t := Fin.ext (Nat.mod_eq_of_lt short)
    have nz : t ≠ 0 := fun eq => (Nat.ne_of_gt pos) (congrArg Fin.val eq)
    obtain ⟨v, hv⟩ := early_disagreement t nz
    rw [all_ticks, pt] at h
    exact hv (congrFun h v)

theorem thirty_five_chips : (List.ofFn initial).sum = 35 := by decide

/-- The finite one-tick transition table on the recurrent orbit. -/
def clockNext (t : Fin 18) : Fin 18 := phase (t.val+1)

theorem clock_table_faithful : Function.Injective trace ∧
    ∀ t, step graph (trace t) = trace (clockNext t) := by
  refine ⟨?_, step_trace⟩
  have distinguished : ∀ i j : Fin 18, i ≠ j → ∃ v : Fin 34, trace i v ≠ trace j v := by
    decide
  intro i j same
  by_contra diff
  obtain ⟨v, hv⟩ := distinguished i j diff
  exact hv (congrFun same v)

theorem mass_at_every_tick (t : ℕ) : (List.ofFn (after graph initial t)).sum = 35 := by
  have masses : ∀ i : Fin 18, (List.ofFn (trace i)).sum = 35 := by decide
  rw [all_ticks]
  exact masses _

private def routeOK {n : ℕ} (G : Table n) (target : Fin n) :
    Fin n → List (Fin n) → Bool
  | u, [] => decide (u = target)
  | u, v :: rest => decide (v ∈ G u) && routeOK G target v rest

private theorem reaches_trans {n : ℕ} {G : Table n} {u v w : Fin n}
    (a : Reaches G u v) (b : Reaches G v w) : Reaches G u w := by
  induction b with
  | refl => exact a
  | extend _ edge ih => exact .extend ih edge

private theorem route_sound {n : ℕ} (G : Table n) (target u : Fin n)
    (r : List (Fin n)) (h : routeOK G target u r = true) : Reaches G u target := by
  induction r generalizing u with
  | nil =>
    have e : u = target := of_decide_eq_true h
    subst target
    exact .refl _
  | cons v rest ih =>
    obtain ⟨edge, later⟩ := Bool.and_eq_true_iff.mp h
    exact reaches_trans (.extend (.refl _) (of_decide_eq_true edge)) (ih v later)

theorem simple_connected : IsSimpleConnected graph := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have routes : ∀ v : Fin 34, routeOK graph v 33 (hubPath v).tail = true ∧
      routeOK graph 33 v (hubPath v).reverse.tail = true := by decide
  intro u v
  exact reaches_trans (route_sound _ _ _ _ (routes u).2) (route_sound _ _ _ _ (routes v).1)

private def allowed (k : ℕ) : Bool := decide (k = 2 ∨ k = 6 ∨ k = 27)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem scan_graph : ∀ s : Fin 34, scan graph s allowed 34 s [s] = true := by
  decide

theorem subcycle_lengths (c : List (Fin 34)) (h : IsSubcycle graph c) :
    c.length = 2 ∨ c.length = 6 ∨ c.length = 27 :=
  of_decide_eq_true (lengths_from_scan graph allowed scan_graph c h)

theorem simple_cycle_lengths (c : List (Fin 34)) (h : IsSimpleCycle graph c) :
    c.length = 6 ∨ c.length = 27 := by
  have hlen := subcycle_lengths c h.1
  have ge := h.2
  omega

theorem both_rings_exist :
    (∃ c, IsSimpleCycle graph c ∧ c.length = 6) ∧
    (∃ c, IsSimpleCycle graph c ∧ c.length = 27) := by
  constructor
  · refine ⟨[0,1,2,3,4,5], ?_⟩
    simp [IsSimpleCycle, IsSubcycle, Closes, graph]
  · refine ⟨[6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32], ?_⟩
    simp [IsSimpleCycle, IsSubcycle, Closes, graph]

private theorem permitted_lcms (xs : List ℕ) (h : ∀ k ∈ xs, k = 2 ∨ k = 6 ∨ k = 27) :
    xs.foldr Nat.lcm 1 ∈ [1,2,6,27,54] := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have first := h x (by simp)
    have rest := ih fun k hk => h k (by simp [hk])
    simp only [List.foldr_cons]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rest
    rcases first with rfl | rfl | rfl <;>
      rcases rest with h | h | h | h | h <;> rw [h] <;> decide

/-- This obstruction holds for every list of subcycles, even with repeats
or intersections. -/
theorem lcm_ne_eighteen (cs : List (List (Fin 34)))
    (h : ∀ c ∈ cs, IsSubcycle graph c) : cycleLcm cs ≠ 18 := by
  have bound := permitted_lcms (cs.map List.length) (by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    exact subcycle_lengths c (h _ hc))
  intro eq
  change (cs.map List.length).foldr Nat.lcm 1 = 18 at eq
  rw [eq] at bound
  exact (by decide : 18 ∉ ([1,2,6,27,54] : List ℕ)) bound

private theorem no_explanation (cyc : List (Fin 34) → Prop)
    (sub : ∀ c, cyc c → IsSubcycle graph c) : ¬ ExplainedBy cyc 18 := by
  rintro (⟨c, hc, hd⟩ | ⟨cs, hcs, _, heq⟩)
  · rcases subcycle_lengths c (sub c hc) with h | h | h <;> rw [h] at hd <;> omega
  · exact lcm_ne_eighteen cs (fun c hc => sub c (hcs c hc)) heq

/-- A direct negation of the universal conjecture, for both cycle conventions. -/
theorem not_jiang_cycle_conjecture (allowBacktracks : Bool) :
    ¬ JiangCycleConjecture allowBacktracks := by
  intro statement
  have hperiod : EventualPeriod graph initial 18 := ⟨0, exact_period_eighteen⟩
  have claimed := statement 34 graph simple_connected initial 18 hperiod
  cases allowBacktracks with
  | false => exact no_explanation _ (fun _ h => h.1) claimed
  | true => exact no_explanation _ (fun _ h => h) claimed

end ClockedChipFiring
