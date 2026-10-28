import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectArgmin

namespace OAI.Algorithms

/-! The finite greedy algorithm and bounds for every trial, including
losing candidates. The evaluator is an explicit input function; exactness
is a theorem hypothesis to be discharged by the actual sparse evaluator. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R : Type*} {c : ℕ}

def next (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (rows : List R) : List R :=
  pick (fun r => evaluate (r :: rows)) family :: rows

def run (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) : ℕ → List R
  | 0 => initial
  | t + 1 => next evaluate family (run evaluate family initial t)

def trials (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (rows : List R) : List (List R) :=
  (pickTrace (fun r => evaluate (r :: rows)) family).map (fun r => r :: rows)

def allTrials (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) : ℕ → List (List R)
  | 0 => []
  | t + 1 => allTrials evaluate family initial t ++
      trials evaluate family (run evaluate family initial t)

@[simp] theorem run_length (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (t : ℕ) :
    (run evaluate family initial t).length = initial.length + t := by
  induction t with
  | zero => simp [run]
  | succ t ih => simp [run, next, ih, Nat.add_assoc]

@[simp] theorem trials_length (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (rows : List R) :
    (trials evaluate family rows).length = 2 * (c + 1) := by
  simp [trials, pickTrace_length]

@[simp] theorem allTrials_length (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (t : ℕ) :
    (allTrials evaluate family initial t).length = 2 * (c + 1) * t := by
  induction t with
  | zero => simp [allTrials]
  | succ t ih => simp [allTrials, ih, Nat.mul_add]

def totalCost (cost : R → ℕ) (rows : List R) : ℕ :=
  (rows.map cost).sum

@[simp] theorem totalCost_cons (cost : R → ℕ) (r : R) (rows : List R) :
    totalCost cost (r :: rows) = cost r + totalCost cost rows := by
  simp [totalCost]

theorem run_cost (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hcost : ∀ i, cost (family i) ≤ d) :
    totalCost cost (run evaluate family initial t) ≤ totalCost cost initial + t * d := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
    have h := pick_property (fun r => evaluate (r :: run evaluate family initial t))
      family (fun r => cost r ≤ d) hcost
    simp only [run, next, totalCost_cons]
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add h ih
      _ = totalCost cost initial + (t + 1) * d := by ring

theorem run_property (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (P : R → Prop)
    (hinit : ∀ r ∈ initial, P r) (hfamily : ∀ i, P (family i)) (t : ℕ) :
    ∀ r ∈ run evaluate family initial t, P r := by
  induction t with
  | zero => exact hinit
  | succ t ih =>
    intro r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact pick_property _ family P hfamily
    · exact ih r hr

theorem run_accepts_initial (rowAccept : R → X → Bool)
    (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (t : ℕ) (x : X) :
    accepts rowAccept (run evaluate family initial t) x = true →
      accepts rowAccept initial x = true := by
  induction t with
  | zero => exact id
  | succ t ih =>
    intro h
    apply ih
    exact (Bool.and_eq_true_iff.mp h).2

theorem trial_bounds (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hcost : ∀ i, cost (family i) ≤ d) (q : List R)
    (hq : q ∈ trials evaluate family (run evaluate family initial t)) :
    q.length = initial.length + t + 1 ∧
      totalCost cost q ≤ totalCost cost initial + (t + 1) * d := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hc := pickTrace_property (fun r => evaluate (r :: run evaluate family initial t))
    family (fun r => cost r ≤ d) hcost r hr
  constructor
  · simp [Nat.add_assoc]
  · rw [totalCost_cons]
    have hrun := run_cost evaluate family initial cost d t hcost
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add hc hrun
      _ = _ := by ring

theorem candidate_trial_bounds (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hcost : ∀ i, cost (family i) ≤ d) (i : Fin (c + 1)) :
    (family i :: run evaluate family initial t).length = initial.length + t + 1 ∧
      totalCost cost (family i :: run evaluate family initial t) ≤
        totalCost cost initial + (t + 1) * d := by
  constructor
  · simp [Nat.add_assoc]
  · rw [totalCost_cons]
    have hrun := run_cost evaluate family initial cost d t hcost
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add (hcost i) hrun
      _ = _ := by ring

theorem next_contraction [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (family : Fin (c + 1) → R) (rows : List R)
    (hsound : ∀ i, evaluate (family i :: rows) = mass rowAccept weight (family i :: rows))
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * mass rowAccept weight (next evaluate family rows) ≤
      2 * mass rowAccept weight rows := by
  let score : R → ℕ := fun r => evaluate (r :: rows)
  obtain ⟨j, hj⟩ := pick_mem score family
  have hmin : ∀ i, mass rowAccept weight (next evaluate family rows) ≤
      mass rowAccept weight (family i :: rows) := by
    intro i
    have h := pick_le score family i
    change evaluate (pick score family :: rows) ≤ evaluate (family i :: rows) at h
    rw [hj, hsound j, hsound i] at h
    simpa only [next, score, hj] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmin i)
  have hsum' : (c + 1) * mass rowAccept weight (next evaluate family rows) ≤
      ∑ i, mass rowAccept weight (family i :: rows) := by simpa using hsum
  have havg := average_trial_contraction rowAccept weight family rows
    (by simpa using hcoverage)
  have hmul : (c + 1) * (3 * mass rowAccept weight (next evaluate family rows)) ≤
      (c + 1) * (2 * mass rowAccept weight rows) := by
    calc
      _ = 3 * ((c + 1) * mass rowAccept weight (next evaluate family rows)) := by ring
      _ ≤ 3 * (∑ i, mass rowAccept weight (family i :: rows)) :=
        Nat.mul_le_mul_left 3 hsum'
      _ ≤ 2 * Fintype.card (Fin (c + 1)) * mass rowAccept weight rows := havg
      _ = _ := by simp; ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
