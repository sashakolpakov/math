import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSuccessor

namespace OAI.Algorithms

/-!
# Exact order of the remaining-budget exponent successor

The observed states are exactly the existing degree-budget enumeration, with
coordinates reversed for the stack representation. The final successor call
returns `none`. No enumeration of a coordinate box is used in this proof or
in the successor algorithm.
-/

namespace SubexponentialSAT.SubexpExponentOrder

open scoped BigOperators
open SubexpExponentSuccessor

abbrev State := List ℕ × ℕ

/-- An observation list records the state before every actual successor call,
including the final call which reports exhaustion. -/
inductive Visits : Option State → List State → Option State → Prop
  | nil (state : Option State) : Visits state [] state
  | cons (state : State) {states : List State} {last : Option State} :
      Visits (nextDigits state.1 state.2) states last →
      Visits (some state) (state :: states) last

theorem Visits.append {first middle last : Option State} {xs ys : List State}
    (h : Visits first xs middle) (h' : Visits middle ys last) :
    Visits first (xs ++ ys) last := by
  induction h with
  | nil => exact h'
  | cons state _ ih => exact .cons state (ih h')

/-- Enumerate successive values of one slower coordinate, using the supplied
enumerator for all faster coordinates. This helper is used to prove order. -/
def blocks (enumerate : ℕ → List ℕ → List State) : ℕ → ℕ → List ℕ → List State
  | 0, value, suffix => enumerate 0 (value :: suffix)
  | remaining + 1, value, suffix =>
      enumerate (remaining + 1) (value :: suffix) ++ blocks enumerate remaining (value + 1) suffix

def states : ℕ → ℕ → List ℕ → List State
  | 0, budget, suffix => [(suffix, budget)]
  | dimension + 1, budget, suffix => blocks (states dimension) budget 0 suffix

/-- The helper uses the same increasing range and remaining budget as
`Algorithm.exponentList`. -/
theorem blocks_eq_range (enumerate : ℕ → List ℕ → List State)
    (remaining value : ℕ) (suffix : List ℕ) :
    blocks enumerate remaining value suffix =
      (List.range' value (remaining + 1)).flatMap fun a =>
        enumerate (value + remaining - a) (a :: suffix) := by
  induction remaining generalizing value with
  | zero => simp [blocks]
  | succ remaining ih =>
      rw [blocks, List.range'_succ, List.flatMap_cons, ih]
      congr 1
      · congr 1; omega
      · congr 1
        funext a
        congr 1; omega

theorem states_eq_exponentList (dimension budget : ℕ) (suffix : List ℕ) :
    states dimension budget suffix =
      (Algorithm.exponentList dimension budget).map fun a =>
        ((List.ofFn a).reverse ++ suffix, budget - ∑ i, a i) := by
  induction dimension generalizing budget suffix with
  | zero => simp [states, Algorithm.exponentList]
  | succ dimension ih =>
      simp only [states, blocks_eq_range, Nat.zero_add, List.range_eq_range',
        Algorithm.exponentList, List.map_flatMap, List.map_map, Function.comp_def]
      apply List.flatMap_congr
      intro a ha
      rw [ih]
      apply List.map_congr_left
      intro v hv
      simp [List.ofFn_succ, List.reverse_cons, List.append_assoc,
        Fin.sum_univ_succ, Nat.sub_sub]

private def prependZeroes (dimension : ℕ) (state : State) : State :=
  (List.replicate dimension 0 ++ state.1, state.2)

private theorem prependZeroes_zero : prependZeroes 0 = id := by
  funext state
  cases state
  rfl

private theorem prependZeroes_cons (dimension : ℕ) (state : State) :
    prependZeroes dimension (0 :: state.1, state.2) = prependZeroes (dimension + 1) state := by
  simp [prependZeroes, List.replicate_succ', List.append_assoc]

private theorem blocks_visits (dimension : ℕ)
    (ih : ∀ budget suffix,
      Visits (some (List.replicate dimension 0 ++ suffix, budget))
        (states dimension budget suffix)
        ((nextDigits suffix budget).map (prependZeroes dimension)))
    (remaining value : ℕ) (suffix : List ℕ) :
    Visits (some (List.replicate dimension 0 ++ value :: suffix, remaining))
      (blocks (states dimension) remaining value suffix)
      ((nextDigits suffix (value + remaining)).map (prependZeroes (dimension + 1))) := by
  induction remaining generalizing value with
  | zero =>
      have h := ih 0 (value :: suffix)
      simpa only [blocks, nextDigits, Option.map_map, Function.comp_def,
        prependZeroes_cons, Nat.add_zero] using h
  | succ remaining tail =>
      have hfirst := ih (remaining + 1) (value :: suffix)
      have htail := tail (value + 1)
      have hfirst' :
          Visits (some (List.replicate dimension 0 ++ value :: suffix, remaining + 1))
            (states dimension (remaining + 1) (value :: suffix))
            (some (List.replicate dimension 0 ++ (value + 1) :: suffix, remaining)) := by
        simpa only [nextDigits, Option.map_some, prependZeroes] using hfirst
      have h := hfirst'.append htail
      simpa only [blocks, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Complete enumeration of faster coordinates can be composed with any
slower suffix. Exhaustion restores the budget before carrying into it. -/
theorem states_visits (dimension budget : ℕ) (suffix : List ℕ) :
    Visits (some (List.replicate dimension 0 ++ suffix, budget))
      (states dimension budget suffix)
      ((nextDigits suffix budget).map (prependZeroes dimension)) := by
  induction dimension generalizing budget suffix with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, states, prependZeroes_zero,
        Option.map_id_fun, id_eq] using Visits.cons (suffix, budget) (Visits.nil _)
  | succ dimension ih =>
      have h := blocks_visits dimension ih budget 0 suffix
      simpa only [states, Nat.zero_add, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-- This is the exact existing exponent order, not just a cardinality or
coverage result. Digits are reversed only to match the successor's stack ABI. -/
theorem exponentList_visits (dimension budget : ℕ) :
    Visits (some (List.replicate dimension 0, budget))
      ((Algorithm.exponentList dimension budget).map fun a =>
        ((List.ofFn a).reverse, budget - ∑ i, a i)) none := by
  have h := states_visits dimension budget []
  simpa only [states_eq_exponentList, List.append_nil, nextDigits, Option.map_none] using h

/-- Every visited state retains the exact coordinate count and conserves
the sum of used and unused degree budget. -/
theorem observation_bounds {dimension budget : ℕ} {state : State}
    (hstate : state ∈ (Algorithm.exponentList dimension budget).map fun a =>
      ((List.ofFn a).reverse, budget - ∑ i, a i)) :
    state.1.length = dimension ∧ state.1.sum + state.2 = budget := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hstate
  have hdegree := (Algorithm.mem_exponentList dimension budget a).mp ha
  constructor
  · simp
  · simp only [List.sum_reverse, List.sum_ofFn]
    omega

/-- One transition executes one call of the successor function. These are
successor calls; the concrete bit program charges each call separately. -/
def step : Option State → Option (Option State)
  | none => none
  | some state => some (nextDigits state.1 state.2)

theorem Visits.trace {first last : Option State} {observed : List State}
    (h : Visits first observed last) : Computation.Trace step observed.length first last := by
  induction h with
  | nil state => exact .refl state
  | cons state _ ih => exact .cons rfl ih

/-- Exactly one successor call per bounded-degree exponent vector, including
the final exhaustion call. No rejected coordinate-box vectors are charged. -/
theorem exponentList_trace (dimension budget : ℕ) :
    Computation.Trace step ((dimension + budget).choose dimension)
      (some (List.replicate dimension 0, budget)) none := by
  have h := (exponentList_visits dimension budget).trace
  simpa only [List.length_map, Algorithm.exponentList_length] using h

end SubexponentialSAT.SubexpExponentOrder

end OAI.Algorithms
