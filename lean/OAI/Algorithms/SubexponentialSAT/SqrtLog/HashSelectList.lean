import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination

namespace OAI.Algorithms

/-! A payload-list implementation may enumerate tuple rows in any order,
and may repeat them. Surjective coverage, rather than a chosen tie order,
is sufficient for the mass contraction proof. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R P : Type*} {c : ℕ}

def listStep (evaluate : List R → ℕ) (decode : P → R) (seed : P)
    (rest : List P) (rows : List R) : List R :=
  decode (best (fun p => evaluate (decode p :: rows)) seed rest) :: rows

def listRun (evaluate : List R → ℕ) (decode : P → R) (seed : P)
    (rest : List P) (initial : List R) : ℕ → List R
  | 0 => initial
  | t + 1 => listStep evaluate decode seed rest (listRun evaluate decode seed rest initial t)

theorem best_le_of_mem (score : P → ℕ) (seed : P) (rest : List P)
    (p : P) (hp : p ∈ seed :: rest) : score (best score seed rest) ≤ score p := by
  rcases List.mem_cons.mp hp with h | h
  · subst p
    exact best_le_seed score seed rest
  · exact best_le_member score seed rest p h

theorem listStep_contraction [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (decode : P → R) (seed : P) (rest : List P)
    (family : Fin (c + 1) → R) (rows : List R)
    (hcover : ∀ i, ∃ p ∈ seed :: rest, decode p = family i)
    (hsound : ∀ p ∈ seed :: rest,
      evaluate (decode p :: rows) = mass rowAccept weight (decode p :: rows))
    (hcoverage : ∀ x, accepts rowAccept rows x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    3 * mass rowAccept weight (listStep evaluate decode seed rest rows) ≤
      2 * mass rowAccept weight rows := by
  let score := fun p => evaluate (decode p :: rows)
  have hchosen := hsound (best score seed rest) (best_mem score seed rest)
  have hmin : ∀ i, mass rowAccept weight (listStep evaluate decode seed rest rows) ≤
      mass rowAccept weight (family i :: rows) := by
    intro i
    obtain ⟨p, hp, heq⟩ := hcover i
    have h := best_le_of_mem score seed rest p hp
    change evaluate (decode (best score seed rest) :: rows) ≤
      evaluate (decode p :: rows) at h
    rw [hchosen, hsound p hp, heq] at h
    exact h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmin i)
  have hsum' : (c + 1) * mass rowAccept weight (listStep evaluate decode seed rest rows) ≤
      ∑ i, mass rowAccept weight (family i :: rows) := by simpa using hsum
  have havg := average_trial_contraction rowAccept weight family rows
    (by simpa using hcoverage)
  have hmul : (c + 1) * (3 * mass rowAccept weight (listStep evaluate decode seed rest rows)) ≤
      (c + 1) * (2 * mass rowAccept weight rows) := by
    calc
      _ = 3 * ((c + 1) * mass rowAccept weight (listStep evaluate decode seed rest rows)) := by ring
      _ ≤ 3 * (∑ i, mass rowAccept weight (family i :: rows)) := Nat.mul_le_mul_left 3 hsum'
      _ ≤ 2 * (c + 1) * mass rowAccept weight rows := by simpa using havg
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

@[simp] theorem listRun_length (evaluate : List R → ℕ) (decode : P → R)
    (seed : P) (rest : List P) (initial : List R) (t : ℕ) :
    (listRun evaluate decode seed rest initial t).length = initial.length + t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [listRun, listStep, ih, Nat.add_assoc]

theorem listRun_accepts_initial (rowAccept : R → X → Bool)
    (evaluate : List R → ℕ) (decode : P → R) (seed : P) (rest : List P)
    (initial : List R) (t : ℕ) (x : X) :
    accepts rowAccept (listRun evaluate decode seed rest initial t) x = true →
      accepts rowAccept initial x = true := by
  induction t with
  | zero => exact id
  | succ t ih =>
    intro h
    exact ih (Bool.and_eq_true_iff.mp h).2

theorem listRun_property (evaluate : List R → ℕ) (decode : P → R)
    (seed : P) (rest : List P) (initial : List R) (Q : R → Prop)
    (hinit : ∀ r ∈ initial, Q r) (hlist : ∀ p ∈ seed :: rest, Q (decode p)) (t : ℕ) :
    ∀ r ∈ listRun evaluate decode seed rest initial t, Q r := by
  induction t with
  | zero => exact hinit
  | succ t ih =>
    intro r hr
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact hlist _ (best_mem _ seed rest)
    · exact ih r h

theorem listRun_cost (evaluate : List R → ℕ) (decode : P → R)
    (seed : P) (rest : List P) (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hlist : ∀ p ∈ seed :: rest, cost (decode p) ≤ d) :
    totalCost cost (listRun evaluate decode seed rest initial t) ≤
      totalCost cost initial + t * d := by
  induction t with
  | zero => simp [listRun]
  | succ t ih =>
    have h := hlist _ (best_mem (fun p => evaluate
      (decode p :: listRun evaluate decode seed rest initial t)) seed rest)
    simp only [listRun, listStep, totalCost_cons]
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add h ih
      _ = _ := by ring

theorem list_candidate_bounds (evaluate : List R → ℕ) (decode : P → R)
    (seed : P) (rest : List P) (initial : List R) (cost : R → ℕ) (d t : ℕ)
    (hlist : ∀ p ∈ seed :: rest, cost (decode p) ≤ d)
    (p : P) (hp : p ∈ seed :: rest) :
    (decode p :: listRun evaluate decode seed rest initial t).length = initial.length + t + 1 ∧
    totalCost cost (decode p :: listRun evaluate decode seed rest initial t) ≤
      totalCost cost initial + (t + 1) * d := by
  constructor
  · simp [Nat.add_assoc]
  · rw [totalCost_cons]
    have hs := listRun_cost evaluate decode seed rest initial cost d t hlist
    calc
      _ ≤ d + (totalCost cost initial + t * d) := Nat.add_le_add (hlist p hp) hs
      _ = _ := by ring

theorem list_candidate_property (evaluate : List R → ℕ) (decode : P → R)
    (seed : P) (rest : List P) (initial : List R) (Q : R → Prop)
    (hinit : ∀ r ∈ initial, Q r) (hlist : ∀ p ∈ seed :: rest, Q (decode p))
    (t : ℕ) (p : P) (hp : p ∈ seed :: rest) :
    ∀ r ∈ decode p :: listRun evaluate decode seed rest initial t, Q r := by
  intro r hr
  rcases List.mem_cons.mp hr with h | h
  · subst r
    exact hlist p hp
  · exact listRun_property evaluate decode seed rest initial Q hinit hlist t r h

theorem listRun_zero [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ)
    (evaluate : List R → ℕ) (decode : P → R) (seed : P) (rest : List P)
    (family : Fin (c + 1) → R) (initial : List R) (n m : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m)
    (hcover : ∀ i, ∃ p ∈ seed :: rest, decode p = family i)
    (hsound : ∀ t < loopCap n m, ∀ p ∈ seed :: rest,
      evaluate (decode p :: listRun evaluate decode seed rest initial t) =
        mass rowAccept weight (decode p :: listRun evaluate decode seed rest initial t))
    (hcoverage : ∀ x, accepts rowAccept initial x = true → 0 < weight x →
      3 * survivingCandidates rowAccept family x ≤ 2 * (c + 1)) :
    mass rowAccept weight (listRun evaluate decode seed rest initial (loopCap n m)) = 0 := by
  apply zero_of_contraction
    (fun t => mass rowAccept weight (listRun evaluate decode seed rest initial t))
    (n + Nat.size m + 1)
  · intro t ht
    apply listStep_contraction rowAccept weight evaluate decode seed rest family _ hcover (hsound t ht)
    intro x ha hp
    exact hcoverage x (listRun_accepts_initial rowAccept evaluate decode seed rest initial t x ha) hp
  · exact initial_mass_lt_cap_power rowAccept weight initial n m hx hw

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
