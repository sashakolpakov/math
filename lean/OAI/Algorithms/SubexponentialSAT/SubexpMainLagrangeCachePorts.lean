import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCachePreparation

namespace OAI.Algorithms

/-!
# Main ports for the physical target Lagrange cache

The eight native inputs are persistent Main words.  Native output250 is
master28 (ordinary668).  Every other native word lies in ordinary320..575,
below the retained layout masters and above the source-field cache.
-/

namespace SubexponentialSAT.SubexpMainLagrangeCache

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLagrangeCachePreparation (Inputs inputWords rawStore)

def inputPort : Fin 8 → Fin 256 := SubexpLagrangeCachePreparation.sourcePorts

def persistentIndex : Fin 8 → Fin 32 := ![6, 30, 12, 13, 14, 31, 22, 29]

def inputIndex (i : Fin 256) : Option (Fin 8) :=
  if i = 206 then some 0 else if i = 207 then some 1 else
  if i = 208 then some 2 else if i = 209 then some 3 else
  if i = 210 then some 4 else if i = 211 then some 5 else
  if i = 224 then some 6 else if i = 225 then some 7 else none

theorem persistentIndex_injective : Function.Injective persistentIndex := by decide

@[simp] theorem inputIndex_inputPort (i : Fin 8) : inputIndex (inputPort i) = some i := by
  fin_cases i <;> rfl

theorem inputIndex_eq_some {i : Fin 256} {j : Fin 8}
    (h : inputIndex i = some j) : i = inputPort j := by
  unfold inputIndex at h
  split_ifs at h <;> simp_all [inputPort, SubexpLagrangeCachePreparation.sourcePorts]
  all_goals subst j; rfl

theorem inputPort_injective : Function.Injective inputPort := by
  intro i j h
  have := congrArg inputIndex h
  simpa only [inputIndex_inputPort, Option.some.injEq] using this

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 256) : Fin (totalStacks es) :=
  match inputIndex i with
  | some j => persistent es (persistentIndex j)
  | none => if i = 250 then master alloc 28
      else ordinary alloc ⟨320 + i.val, by omega⟩

@[simp] theorem stackMap_input {es : ℕ} (alloc : Allocation es) (i : Fin 8) :
    stackMap alloc (inputPort i) = persistent es (persistentIndex i) := by
  simp only [stackMap, inputIndex_inputPort]

@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) :
    stackMap alloc 250 = master alloc 28 := rfl

theorem stackMap_work {es : ℕ} (alloc : Allocation es) (i : Fin 256)
    (hi : inputIndex i = none) (ho : i ≠ 250) :
    stackMap alloc i = ordinary alloc ⟨320 + i.val, by omega⟩ := by
  simp only [stackMap, hi, ite_eq_right ho]

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
  have hw := alloc.enough.trans alloc.within
  cases hi : inputIndex i with
  | some a =>
    cases hj : inputIndex j with
    | some b =>
      have hab : persistentIndex a = persistentIndex b := persistent_injective es (by
        simpa only [stackMap, hi, hj] using h)
      have hab' := persistentIndex_injective hab
      exact (inputIndex_eq_some hi).trans (hab' ▸ (inputIndex_eq_some hj).symm)
    | none =>
      simp only [stackMap, hi, hj, persistent, Fin.val_natAdd] at hv
      split_ifs at hv <;> simp only [SubexpLayoutPorts.master_val, ordinary] at hv <;> omega
  | none =>
    cases hj : inputIndex j with
    | some b =>
      simp only [stackMap, hi, hj, persistent, Fin.val_natAdd] at hv
      split_ifs at hv <;> simp only [SubexpLayoutPorts.master_val, ordinary] at hv <;> omega
    | none =>
      simp only [stackMap, hi, hj] at hv
      split_ifs at hv with hi250 hj250 hj250
      · exact hi250.trans hj250.symm
      · simp only [SubexpLayoutPorts.master_val, ordinary] at hv
        omega
      · simp only [SubexpLayoutPorts.master_val, ordinary] at hv
        omega
      · apply Fin.ext
        simp only [ordinary] at hv
        omega

def sourceInputs {er es : ℕ} (a : MainState er es) : Inputs where
  prime := a.stacks (persistent es 6)
  unit := a.stacks (persistent es 30)
  modulus := a.stacks (persistent es 12)
  width := a.stacks (persistent es 13)
  reduction := a.stacks (persistent es 14)
  minusOne := a.stacks (persistent es 31)
  precision := a.stacks (persistent es 22)
  exponent := a.stacks (persistent es 29)

@[simp] theorem sourceInputs_word {er es : ℕ} (a : MainState er es) (i : Fin 8) :
    inputWords (sourceInputs a) i = a.stacks (persistent es (persistentIndex i)) := by
  fin_cases i <;> rfl

theorem rawStore_input (x : Inputs) (i : Fin 8) :
    rawStore x (inputPort i) = inputWords x i := by
  fin_cases i <;> rfl

theorem rawStore_other (x : Inputs) (i : Fin 256) (hi : inputIndex i = none) :
    rawStore x i = [] := by
  unfold inputIndex at hi
  unfold rawStore
  split_ifs at hi ⊢; simp_all

theorem stackMap_avoids_work {es : ℕ} (alloc : Allocation es)
    (i : Fin (totalStacks es)) (hwork : i.val < workStacks es)
    (hrange : i.val < 320 ∨ 576 ≤ i.val) (hout : i.val ≠ 668) :
    ¬ ∃ j, stackMap alloc j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  cases hi : inputIndex j with
  | some a =>
    simp only [stackMap, hi, persistent, Fin.val_natAdd] at hv
    omega
  | none =>
    simp only [stackMap, hi] at hv
    split_ifs at hv
    · simp only [SubexpLayoutPorts.master_val] at hv
      omega
    · simp only [ordinary] at hv
      rcases hrange with hrange | hrange <;> omega

theorem stackMap_eq_persistent {es : ℕ} (alloc : Allocation es)
    {i : Fin 256} {j : Fin 32} (h : stackMap alloc i = persistent es j) :
    ∃ k, i = inputPort k ∧ persistentIndex k = j := by
  have hw := alloc.enough.trans alloc.within
  cases hi : inputIndex i with
  | some k =>
    refine ⟨k, inputIndex_eq_some hi, ?_⟩
    exact persistent_injective es (by simpa only [stackMap, hi] using h)
  | none =>
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
    simp only [stackMap, hi, persistent, Fin.val_natAdd] at hv
    split_ifs at hv <;> simp only [SubexpLayoutPorts.master_val, ordinary] at hv <;> omega

end SubexponentialSAT.SubexpMainLagrangeCache

end OAI.Algorithms
