import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination
import Mathlib.Data.List.Range

/-! The streamed strict argmin and its greedy invariant. Candidate indices describe
an iterator's successive callbacks; no list of candidates is constructed here.
The finite-program implementation must refine these recurrences. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy

open OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect
open scoped BigOperators

variable {R X : Type*}

/-- One cached-score update. Equal scores retain the earlier candidate. -/
def update (best : R × ℕ) (candidate : R) (score : ℕ) : R × ℕ :=
  if score < best.2 then (candidate, score) else best

/-- Result after the seed and the next `t` candidates have been evaluated. -/
def scan (evaluate : R → ℕ) (candidate : ℕ → R) : ℕ → R × ℕ
  | 0 => (candidate 0, evaluate (candidate 0))
  | t + 1 => update (scan evaluate candidate t)
      (candidate (t + 1)) (evaluate (candidate (t + 1)))

@[simp] theorem update_score (best : R × ℕ) (candidate : R) (score : ℕ) :
    (update best candidate score).2 = min best.2 score := by
  unfold update
  split_ifs with h
  · exact (Nat.min_eq_right (Nat.le_of_lt h)).symm
  · exact (Nat.min_eq_left (Nat.le_of_not_gt h)).symm

@[simp] theorem scan_score (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).2 = evaluate (scan evaluate candidate t).1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [scan, update]
    split_ifs <;> simp_all

theorem scan_selected (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    ∃ j ≤ t, (scan evaluate candidate t).1 = candidate j := by
  induction t with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ t ih =>
    simp only [scan, update]
    split_ifs
    · exact ⟨t + 1, le_rfl, rfl⟩
    · obtain ⟨j, hj, he⟩ := ih
      exact ⟨j, hj.trans (Nat.le_succ t), he⟩

theorem scan_le (evaluate : R → ℕ) (candidate : ℕ → R) (t j : ℕ) (hj : j ≤ t) :
    (scan evaluate candidate t).2 ≤ evaluate (candidate j) := by
  induction t with
  | zero => simp [Nat.eq_zero_of_le_zero hj, scan]
  | succ t ih =>
    rw [scan, update_score]
    by_cases h : j ≤ t
    · exact (Nat.min_le_left _ _).trans (ih h)
    · have he : j = t + 1 := by omega
      subst j
      exact Nat.min_le_right _ _


private theorem best_append (evaluate : R → ℕ) (seed : R) (xs ys : List R) :
    best evaluate seed (xs ++ ys) = best evaluate (best evaluate seed xs) ys := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih => exact ih _

/-- The native iterator's proof-only visit log agrees with the indexed scan.
The seed's repeated visit at index zero leaves its cached score unchanged. -/
theorem scan_eq_best (evaluate : R → ℕ) (candidate : ℕ → R) (t : ℕ) :
    (scan evaluate candidate t).1 =
      best evaluate (candidate 0) ((List.range' 0 (t + 1)).map candidate) := by
  induction t with
  | zero => simp [scan, best]
  | succ t ih =>
    rw [List.range'_concat, List.map_append, best_append]
    simp only [Nat.one_mul, Nat.zero_add, List.map_cons, List.map_nil, best, ← ih]
    simp only [scan, update, scan_score]
    split_ifs <;> rfl

/-- The scan pays every score, including all losing candidates, once. -/
def scoreCost (cost : ℕ → ℕ) : ℕ → ℕ
  | 0 => cost 0
  | t + 1 => scoreCost cost t + cost (t + 1)

theorem scoreCost_eq_sum (cost : ℕ → ℕ) (t : ℕ) :
    scoreCost cost t = ∑ j ∈ Finset.range (t + 1), cost j := by
  induction t with
  | zero => simp [scoreCost]
  | succ t ih => simp [scoreCost, Finset.sum_range_succ, ih]

theorem scoreCost_le (cost : ℕ → ℕ) (t budget : ℕ)
    (h : ∀ j ≤ t, cost j ≤ budget) : scoreCost cost t ≤ (t + 1) * budget := by
  rw [scoreCost_eq_sum]
  calc
    _ ≤ ∑ _j ∈ Finset.range (t + 1), budget :=
      Finset.sum_le_sum fun j hj => h j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp


/-- Cost across all rounds, including scores of rows that are rejected. -/
def selectionCost (cost : ℕ → ℕ → ℕ) (last : ℕ) : ℕ → ℕ
  | 0 => 0
  | rounds + 1 => selectionCost cost last rounds + scoreCost (cost rounds) last

theorem selectionCost_le (cost : ℕ → ℕ → ℕ) (last rounds budget : ℕ)
    (h : ∀ t < rounds, ∀ j ≤ last, cost t j ≤ budget) :
    selectionCost cost last rounds ≤ rounds * (last + 1) * budget := by
  induction rounds with
  | zero => simp [selectionCost]
  | succ rounds ih =>
    have hprevious := ih (fun t ht => h t (by omega))
    have hcurrent := scoreCost_le (cost rounds) last budget (h rounds (by omega))
    simp only [selectionCost]
    calc
      _ ≤ rounds * (last + 1) * budget + (last + 1) * budget :=
        Nat.add_le_add hprevious hcurrent
      _ = _ := by ring

/-- Averaging is over the reference ternary family, regardless of duplicates
or order in the stream used to find the minimizing row. -/
theorem contraction_of_minimum [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (family : Fin (c + 1) → R) (rows : List R) (selected : R)
    (hmin : ∀ i, mass rowAccept weight (selected :: rows) ≤
      mass rowAccept weight (family i :: rows))
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * mass rowAccept weight (selected :: rows) ≤ 2 * mass rowAccept weight rows := by
  have hsum : (c + 1) * mass rowAccept weight (selected :: rows) ≤
      ∑ i, mass rowAccept weight (family i :: rows) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmin i)
  have havg := average_trial_contraction rowAccept weight family rows
    (by simpa using hcoverage)
  have hmul : (c + 1) * (3 * mass rowAccept weight (selected :: rows)) ≤
      (c + 1) * (2 * mass rowAccept weight rows) := by
    calc
      _ = 3 * ((c + 1) * mass rowAccept weight (selected :: rows)) := by ring
      _ ≤ 3 * (∑ i, mass rowAccept weight (family i :: rows)) :=
        Nat.mul_le_mul_left 3 hsum
      _ ≤ 2 * Fintype.card (Fin (c + 1)) * mass rowAccept weight rows := havg
      _ = _ := by simp; ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- Reference coverage suffices even if the streamed decoder repeats rows. -/
theorem scan_contraction [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (family : Fin (c + 1) → R) (rows : List R)
    (hsound : ∀ j ≤ last,
      evaluate (candidate j) = mass rowAccept weight (candidate j :: rows))
    (hcover : ∀ i, ∃ j ≤ last, candidate j = family i)
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * mass rowAccept weight ((scan evaluate candidate last).1 :: rows) ≤
      2 * mass rowAccept weight rows := by
  obtain ⟨j, hj, hselected⟩ := scan_selected evaluate candidate last
  have hmin : ∀ i, mass rowAccept weight ((scan evaluate candidate last).1 :: rows) ≤
      mass rowAccept weight (family i :: rows) := by
    intro i
    obtain ⟨l, hl, hli⟩ := hcover i
    have h := scan_le evaluate candidate last l hl
    rw [scan_score, hselected, hsound j hj, hsound l hl, hli] at h
    simpa only [hselected] using h
  exact contraction_of_minimum rowAccept weight family rows
    (scan evaluate candidate last).1 hmin hcoverage

/-- Selected rows are the only persistent history; trials are not retained. -/
def history (evaluate : List R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (initial : List R) : ℕ → List R
  | 0 => initial
  | t + 1 =>
    let rows := history evaluate candidate last initial t
    (scan (fun r => evaluate (r :: rows)) candidate last).1 :: rows

@[simp] theorem history_length (evaluate : List R → ℕ) (candidate : ℕ → R)
    (last : ℕ) (initial : List R) (t : ℕ) :
    (history evaluate candidate last initial t).length = initial.length + t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [history, ih, Nat.add_assoc]

theorem history_accepts_initial (rowAccept : R → X → Bool)
    (evaluate : List R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (initial : List R) (t : ℕ) (x : X) :
    accepts rowAccept (history evaluate candidate last initial t) x = true →
      accepts rowAccept initial x = true := by
  induction t with
  | zero => exact id
  | succ t ih =>
    intro h
    exact ih (Bool.and_eq_true_iff.mp h).2

theorem history_cost (evaluate : List R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hcost : ∀ j ≤ last, cost (candidate j) ≤ d) :
    totalCost cost (history evaluate candidate last initial t) ≤
      totalCost cost initial + t * d := by
  induction t with
  | zero => simp [history]
  | succ t ih =>
    obtain ⟨j, hj, he⟩ := scan_selected
      (fun r => evaluate (r :: history evaluate candidate last initial t)) candidate last
    simp only [history, totalCost_cons]
    rw [he]
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add (hcost j hj) ih
      _ = _ := by ring

/-- This includes every candidate query, not only the selected row. -/
theorem trial_cost (evaluate : List R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (initial : List R) (cost : R → ℕ) (d t j : ℕ) (hj : j ≤ last)
    (hcost : ∀ i ≤ last, cost (candidate i) ≤ d) :
    totalCost cost (candidate j :: history evaluate candidate last initial t) ≤
      totalCost cost initial + (t + 1) * d := by
  rw [totalCost_cons]
  have h := history_cost evaluate candidate last initial cost d t hcost
  calc
    _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add (hcost j hj) h
    _ = _ := by ring

theorem history_mass_zero [Fintype X] {c : ℕ}
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (candidate : ℕ → R) (last : ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hsound : ∀ t < loopCap n m, ∀ j ≤ last,
      evaluate (candidate j :: history evaluate candidate last initial t) =
        mass rowAccept weight (candidate j :: history evaluate candidate last initial t))
    (hcover : ∀ i, ∃ j ≤ last, candidate j = family i)
    (hcoverage : ∀ x, accepts rowAccept initial x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    mass rowAccept weight (history evaluate candidate last initial (loopCap n m)) = 0 := by
  apply zero_of_contraction
    (fun t => mass rowAccept weight (history evaluate candidate last initial t))
    (n + Nat.size m + 1)
  · intro t ht
    apply scan_contraction rowAccept weight _ candidate last family _ (hsound t ht) hcover
    intro x ha hp
    exact hcoverage x
      (history_accepts_initial rowAccept evaluate candidate last initial t x ha) hp
  · exact initial_mass_lt_cap_power rowAccept weight initial n m hx hw

/-- The retained unary round-count word is a sufficient common score width,
including weighted violation mass with up to `m` contributions per assignment. -/
theorem mass_lt_loopCap_capacity [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (rows : List R) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows < 2 ^ loopCap n m := by
  apply (initial_mass_lt_cap_power rowAccept weight rows n m hx hw).trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold loopCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
