import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorOutput
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! The encoded first-match selector implements the actual local read-plan
index map, using an explicit table and a unary query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpRecordScan

def unaryIndex (n : ℕ) : List Bool := List.replicate n true

@[simp] theorem unaryIndex_length (n : ℕ) : (unaryIndex n).length = n := by
  simp [unaryIndex]

@[simp] theorem unaryIndex_reverse (n : ℕ) : (unaryIndex n).reverse = unaryIndex n := by
  simp [unaryIndex]

theorem unaryIndex_injective : Function.Injective unaryIndex := by
  intro m n h
  simpa using congrArg List.length h

def encodeEntries (entries : List (ℕ × ℕ)) : List (List Bool × List Bool) :=
  entries.map (fun p => (unaryIndex p.1, unaryIndex p.2))

theorem encodeEntries_lookup (entries : List (ℕ × ℕ)) (n : ℕ) :
    (encodeEntries entries).lookup (unaryIndex n) =
      (entries.lookup n).map unaryIndex := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
      rcases p with ⟨key, value⟩
      by_cases h : n = key
      · subst key
        simp [encodeEntries ]
      · have hu : unaryIndex n ≠ unaryIndex key := fun he => h (unaryIndex_injective he)
        simpa [encodeEntries, List.lookup_cons, beq_false_of_ne h, beq_false_of_ne hu] using ih

def selectionEntries (currentSize : ℕ) (remaining : List ℕ) :
    List (List Bool × List Bool) :=
  encodeEntries (ReadPlan.selectionTable currentSize remaining)

theorem selectionEntries_lookup_default (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    ((selectionEntries currentSize remaining).lookup (unaryIndex n)).getD (unaryIndex n) =
      unaryIndex (ReadPlan.selectPosition currentSize remaining n) := by
  unfold selectionEntries
  rw [encodeEntries_lookup]
  have h := congrArg unaryIndex (ReadPlan.selectionTable_lookup_default currentSize remaining n)
  cases he : (ReadPlan.selectionTable currentSize remaining).lookup n <;>
    simpa [he] using h

/-- A uniform polynomial bound for the actual key scan. -/
theorem scanBudget_selectionEntries_le (currentSize : ℕ) (remaining : List ℕ) (n K : ℕ)
    (hk : ∀ i ∈ remaining, i ≤ K) :
    scanBudget (unaryIndex n) (selectionEntries currentSize remaining) ≤
      remaining.length *
        (17 * K + 9 * n + 13 * (currentSize + remaining.length) + 40) + 1 := by
  induction remaining generalizing currentSize with
  | nil => simp [selectionEntries, encodeEntries, ReadPlan.selectionTable, scanBudget]
  | cons a remaining ih =>
      have ha : a ≤ K := hk a (by simp)
      have ht := ih (currentSize + 1) (fun i hi => hk i (by simp [hi]))
      change recordCost (unaryIndex a) (unaryIndex n) (unaryIndex currentSize) + 4 +
        scanBudget (unaryIndex n) (selectionEntries (currentSize + 1) remaining) ≤ _
      simp only [recordCost, unaryIndex_length, List.length_cons] at *
      nlinarith

theorem materializeBudget_selectionEntries_le (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    materializeBudget (unaryIndex n) ((selectionEntries currentSize remaining).lookup (unaryIndex n)) ≤
      7 * (n + currentSize + remaining.length) + 6 := by
  rw [selectionEntries, encodeEntries_lookup, ReadPlan.selectionTable_lookup]
  by_cases h : n ∈ remaining
  · have hi : remaining.idxOf n < remaining.length := List.idxOf_lt_length_iff.mpr h
    simp [h, materializeBudget, unaryIndex_length]
    omega
  · simp [h, materializeBudget, unaryIndex_length]
    omega

/-- No exponent in this source-instruction bound depends on the parameters. -/
theorem budget_selectionEntries_le (currentSize : ℕ) (remaining : List ℕ) (n K : ℕ)
    (hk : ∀ i ∈ remaining, i ≤ K) :
    budget (unaryIndex n) (selectionEntries currentSize remaining) ≤
      remaining.length *
        (17 * K + 9 * n + 13 * (currentSize + remaining.length) + 40) +
      7 * (n + currentSize + remaining.length) + 10 := by
  have hs := scanBudget_selectionEntries_le currentSize remaining n K hk
  have hm := materializeBudget_selectionEntries_le currentSize remaining n
  unfold budget
  omega

/-- This is a genuine instruction trace computing the selected current- or
candidate-row index, rather than a unit-cost abstract table lookup. -/
theorem selected_index_trace (currentSize : ℕ) (remaining : List ℕ) (n : ℕ)
    (regs : Fin 5 → Bool) :
    ∃ time ≤ budget (unaryIndex n) (selectionEntries currentSize remaining),
      ∃ regs' tail,
      Trace program time
        ((recordState regs (rawRecords (selectionEntries currentSize remaining))
          [] (unaryIndex n) [] [] []).withPC (some program.entry))
        ((recordState regs' tail
          (unaryIndex (ReadPlan.selectPosition currentSize remaining n))
          (unaryIndex n) [] [] []).withPC none) := by
  simpa only [selectionEntries_lookup_default, unaryIndex_reverse] using
    program_trace (unaryIndex n) (selectionEntries currentSize remaining) regs

theorem selected_index_primitive (currentSize : ℕ) (remaining : List ℕ) (n : ℕ)
    (regs : Fin 5 → Bool) :
    ∃ regs' tail,
      SubexponentialSAT.Computation.RunsIn (BitProgram.primitive program).step
        (primitiveOverhead program * budget (unaryIndex n) (selectionEntries currentSize remaining))
        (primitiveCfg program
          ((recordState regs (rawRecords (selectionEntries currentSize remaining))
            [] (unaryIndex n) [] [] []).withPC (some program.entry)))
        (primitiveCfg program
          ((recordState regs' tail
            (unaryIndex (ReadPlan.selectPosition currentSize remaining n))
            (unaryIndex n) [] [] []).withPC none)) := by
  simpa only [selectionEntries_lookup_default, unaryIndex_reverse] using
    program_primitive (unaryIndex n) (selectionEntries currentSize remaining) regs

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
