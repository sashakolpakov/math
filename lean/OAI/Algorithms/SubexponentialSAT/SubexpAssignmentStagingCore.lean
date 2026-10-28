import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAssignmentSetup

namespace OAI.Algorithms

/-! Fixed physical copies and cleanup for assignment staging. -/

namespace SubexponentialSAT.SubexpAssignmentStaging

open BitProgram StructuredCalls SubexpSetupStorage SubexpAssignmentSetup
open SubexpPreparedSetupCalls (StackBound)
open Subexp
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

abbrev Data := SubexpAssignmentSetup.Data
abbrev Command := SubexpAssignmentSetup.Command

def input (i : Fin 5) : Fin 63 := ⟨51 + i.val, by omega⟩
def outputSource : Fin 3 → Fin 63 := ![8, 30, 10]
def outputTarget : Fin 3 → Fin 63 := ![56, 57, 58]
def outputPairs : List (Fin 63 × Fin 63) := List.ofFn fun i => (outputSource i, outputTarget i)
def headerTarget (i : Fin 4) : Fin 63 := ⟨59 + i.val, by omega⟩
def headerPairs : List (Fin 63 × Fin 63) :=
  List.ofFn fun i => (destination i, headerTarget i)

theorem headerPairs_good : ∀ p ∈ headerPairs,
    p.1 ≠ p.2 ∧ p.1 ≠ 48 ∧ (48 : Fin 63) ≠ p.2 := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  fin_cases i <;> decide
theorem headerPairs_separated : ∀ p ∈ headerPairs, ∀ q ∈ headerPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  fin_cases i <;> fin_cases j <;> decide
theorem headerPairs_nodup : (headerPairs.map Prod.snd).Nodup := by decide

theorem outputPairs_good : ∀ p ∈ outputPairs,
    p.1 ≠ p.2 ∧ p.1 ≠ 48 ∧ (48 : Fin 63) ≠ p.2 := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  fin_cases i <;> decide
theorem outputPairs_separated : ∀ p ∈ outputPairs, ∀ q ∈ outputPairs, p.1 ≠ q.2 := by
  intro p hp q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  fin_cases i <;> fin_cases j <;> decide
theorem outputPairs_nodup : (outputPairs.map Prod.snd).Nodup := by decide

theorem prepared_input (old : Fin 63 → List Bool) (scopes : List (List ℕ)) (i : Fin 5) :
    preparedWords old scopes (input i) = old (input i) := by
  fin_cases i <;> simp [preparedWords, seedWords, input, source, clearedPorts, mem_scratch,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem prepared_empty (old : Fin 63 → List Bool) (scopes : List (List ℕ))
    (j : Fin 63) (hj : j = 48 ∨ j = 49 ∨ j = 50 ∨ 56 ≤ j.val) :
    preparedWords old scopes j = [] := by
  rcases hj with rfl | rfl | rfl | hj
  all_goals try
    simp [preparedWords, seedWords, source, clearedPorts, mem_scratch,
      Fin.ext_iff, Fin.coe_ofNat_eq_mod]
  fin_cases j <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem headerCopy_frame (a : Data) (j : Fin 63) (hj : j.val < 59) :
    (copyManyState headerPairs a).stacks j = a.stacks j := by
  apply copyMany_frame
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  intro he
  have := congrArg (fun x : Fin 63 => x.val) he
  simp only [headerTarget] at this
  omega

def saveHeaders : Command := copyMany 48 headerPairs
def finish : Command := .seq (copyMany 48 outputPairs)
  (.seq (clearMany scratch) RegisterResetProgram.all)
structure Finished (a b : Data) : Prop where
  outputs : ∀ i, b.stacks (outputTarget i) = a.stacks (outputSource i)
  inputs : ∀ i, b.stacks (input i) = a.stacks (input i)
  headers : ∀ i, b.stacks (headerTarget i) = a.stacks (headerTarget i)
  scratch : ∀ j : Fin 63, j.val < 51 → b.stacks j = []
  registers : ∀ j, b.regs j = false

theorem finish_eval (a : Data) (W : ℕ) (ha : StackBound a W)
    (h48 : a.stacks 48 = []) (hblank : ∀ i, a.stacks (outputTarget i) = []) :
    ∃ n b, Eval finish n a b ∧ n ≤ 200 * (W + 1) ∧ StackBound b W ∧ Finished a b := by
  let copied := copyManyState outputPairs a
  let cleared := clearManyState scratch copied
  let b := RegisterResetProgram.zeroed cleared
  have hdest : ∀ p ∈ outputPairs, a.stacks p.2 = [] := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hblank i
  have hcopy := copyMany_eval 48 outputPairs a outputPairs_good h48
  have hcb := SubexpPreparedSetupCalls.copyMany_bound outputPairs a ha
    outputPairs_nodup hdest outputPairs_separated
  have hc := SubexpPreparedSetupCalls.copyManyCost_le outputPairs a
    (fun p _ => ha p.1) outputPairs_separated
  have hclear := SubexpPreparedSetupCalls.clearManyCost_le scratch copied hcb
  have hb := SubexpPreparedSetupCalls.clearMany_bound scratch copied hcb
  refine ⟨copyManyCost outputPairs a + (clearManyCost scratch copied + 16), b,
    hcopy.seq ((clearMany_eval scratch copied).seq (RegisterResetProgram.all_eval cleared)),
    ?_, hb, ?_⟩
  · have hp : outputPairs.length = 3 := by simp [outputPairs]
    have hs : scratch.length = 51 := by simp [SubexpAssignmentSetup.scratch]
    rw [hp] at hc
    rw [hs] at hclear
    omega
  · constructor
    · intro i
      have hout : outputTarget i ∉ scratch := by
        rw [mem_scratch]; fin_cases i <;> decide
      change (clearManyState scratch copied).stacks (outputTarget i) = _
      rw [clearMany_stacks, ite_eq_right hout]
      exact SubexpSetupStorage.copyMany_value outputPairs a outputPairs_nodup hdest
        outputPairs_separated (outputSource i, outputTarget i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · intro i
      change (clearManyState scratch copied).stacks (input i) = _
      rw [clearMany_stacks, ite_eq_right (by rw [mem_scratch]; simp [input])]
      apply copyMany_frame
      intro p hp
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
      fin_cases i <;> fin_cases j <;> decide
    · intro j
      change (clearManyState scratch copied).stacks (headerTarget j) = _
      rw [clearMany_stacks, ite_eq_right (by rw [mem_scratch]; simp only [headerTarget]; omega)]
      apply copyMany_frame
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      fin_cases i <;> fin_cases j <;> decide
    · intro j hj
      change (clearManyState scratch copied).stacks j = []
      rw [clearMany_stacks, ite_eq_left ((mem_scratch j).mpr hj)]
    · intro j; rfl

def wordBound (a : Data) : ℕ := ∑ j : Fin 63, (a.stacks j).length

theorem wordBound_spec (a : Data) : StackBound a (wordBound a) := by
  intro j
  change (a.stacks j).length ≤ ∑ i : Fin 63, (a.stacks i).length
  exact Finset.single_le_sum (f := fun i : Fin 63 => (a.stacks i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)


end SubexponentialSAT.SubexpAssignmentStaging

end OAI.Algorithms
