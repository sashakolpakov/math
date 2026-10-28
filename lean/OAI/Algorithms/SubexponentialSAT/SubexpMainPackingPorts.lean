import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts

namespace OAI.Algorithms

/-! Fixed Main allocation for the physical packing staging program. -/

namespace SubexponentialSAT.SubexpMainPacking

open SubexpMainProgram
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

def inputIndex : Fin 6 → Fin 32 := ![2, 4, 8, 7, 0, 3]
def outputIndex : Fin 6 → Fin 32 := ![15, 16, 13, 17, 18, 19]
def masterIndex : Fin 12 → Fin 32 := ![2, 4, 8, 7, 0, 3, 15, 16, 13, 17, 18, 19]
def writtenMasters : Finset (Fin 32) := {15, 16, 13, 17, 18, 19}

theorem masterIndex_injective : Function.Injective masterIndex := by decide

def calleePort (i : Fin 48) : Fin 61 := i.castAdd 13
def inputPort (i : Fin 6) : Fin 61 := ⟨48 + i.val, by omega⟩
def outputPort (i : Fin 6) : Fin 61 := ⟨54 + i.val, by omega⟩
def temporary : Fin 61 := 60

theorem calleePort_injective : Function.Injective calleePort := Fin.castAdd_injective _ _

def lowPort {es : ℕ} (alloc : Allocation es) (i : Fin 49) : Fin (totalStacks es) :=
  ordinary alloc ⟨i.val, by omega⟩

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 61) : Fin (totalStacks es) :=
  if hlow : i.val < 48 then lowPort alloc ⟨i.val, by omega⟩
  else if hhigh : i.val < 60 then master alloc (masterIndex ⟨i.val - 48, by omega⟩)
  else lowPort alloc 48

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  have hv := congrArg Fin.val h
  by_cases hi : i.val < 48 <;> by_cases hj : j.val < 48
  · apply Fin.ext
    simpa only [stackMap, dite_eq_left hi, dite_eq_left hj, lowPort, ordinary] using hv
  · by_cases hj' : j.val < 60
    · simp only [stackMap, dite_eq_left hi, dite_eq_right hj, dite_eq_left hj', lowPort, ordinary,
        SubexpLayoutPorts.master_val] at hv
      omega
    · simp only [stackMap, dite_eq_left hi, dite_eq_right hj, dite_eq_right hj', lowPort, ordinary] at hv
      norm_num at hv
      omega
  · by_cases hi' : i.val < 60
    · simp only [stackMap, dite_eq_right hi, dite_eq_left hi', dite_eq_left hj, lowPort, ordinary,
        SubexpLayoutPorts.master_val] at hv
      omega
    · simp only [stackMap, dite_eq_right hi, dite_eq_right hi', dite_eq_left hj, lowPort, ordinary] at hv
      norm_num at hv
      omega
  · by_cases hi' : i.val < 60 <;> by_cases hj' : j.val < 60
    · have he := SubexpLayoutPorts.master_injective alloc (by
        simpa only [stackMap, dite_eq_right hi, dite_eq_right hj, dite_eq_left hi', dite_eq_left hj'] using h)
      have he' := congrArg Fin.val (masterIndex_injective he)
      apply Fin.ext
      dsimp only at he'
      omega
    · simp only [stackMap, dite_eq_right hi, dite_eq_right hj, dite_eq_left hi', dite_eq_right hj',
        lowPort, ordinary, SubexpLayoutPorts.master_val] at hv
      norm_num at hv
      omega
    · simp only [stackMap, dite_eq_right hi, dite_eq_right hj, dite_eq_right hi', dite_eq_left hj',
        lowPort, ordinary, SubexpLayoutPorts.master_val] at hv
      norm_num at hv
      omega
    · apply Fin.ext
      omega

@[simp] theorem stackMap_callee {es : ℕ} (alloc : Allocation es) (i : Fin 48) :
    stackMap alloc (calleePort i) = ordinary alloc ⟨i.val, by omega⟩ := by
  unfold stackMap
  have hlow : (calleePort i).val < 48 := i.isLt
  rw [dite_eq_left hlow]
  unfold lowPort
  apply congrArg (ordinary alloc)
  exact Fin.ext rfl

@[simp] theorem stackMap_input {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    stackMap alloc (inputPort i) = master alloc (inputIndex i) := by
  fin_cases i <;> rfl

@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) (i : Fin 6) :
    stackMap alloc (outputPort i) = master alloc (outputIndex i) := by
  fin_cases i <;> rfl

@[simp] theorem stackMap_temporary {es : ℕ} (alloc : Allocation es) :
    stackMap alloc temporary = ordinary alloc 48 := rfl

theorem stackMap_avoids_middle {es : ℕ} (alloc : Allocation es) (j : Fin (totalStacks es))
    (hlo : 49 ≤ j.val) (hhi : j.val < 640) : ¬ ∃ i, stackMap alloc i = j := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  by_cases hlow : i.val < 48
  · simp only [stackMap, dite_eq_left hlow, lowPort, ordinary] at hv
    omega
  by_cases hhigh : i.val < 60
  · simp only [stackMap, dite_eq_right hlow, dite_eq_left hhigh,
      SubexpLayoutPorts.master_val] at hv
    omega
  · simp only [stackMap, dite_eq_right hlow, dite_eq_right hhigh, lowPort, ordinary] at hv
    norm_num at hv
    omega

theorem stackMap_val_lt {es : ℕ} (alloc : Allocation es) (i : Fin 61) :
    (stackMap alloc i).val < 672 := by
  by_cases hlow : i.val < 48
  · simp only [stackMap, dite_eq_left hlow, lowPort, ordinary]
    omega
  by_cases hhigh : i.val < 60
  · have hm := (masterIndex ⟨i.val - 48, by omega⟩).isLt
    simp only [stackMap, dite_eq_right hlow, dite_eq_left hhigh, SubexpLayoutPorts.master_val]
    omega
  · simp [stackMap, hlow, hhigh, lowPort, ordinary]

theorem stackMap_avoids_persistent {es : ℕ} (alloc : Allocation es) (j : Fin 32) :
    ¬ ∃ i, stackMap alloc i = persistent es j := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hm := stackMap_val_lt alloc i
  have ha := alloc.enough.trans alloc.within
  simp only [persistent, Fin.val_natAdd] at hv
  omega

theorem masterIndex_cases (i : Fin 12) :
    (∃ k, inputIndex k = masterIndex i) ∨ masterIndex i ∈ writtenMasters := by
  fin_cases i <;> decide

theorem stackMap_avoids_master {es : ℕ} (alloc : Allocation es) (j : Fin 32)
    (hin : ∀ i, inputIndex i ≠ j) (hout : j ∉ writtenMasters) :
    ¬ ∃ i, stackMap alloc i = master alloc j := by
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  by_cases hlow : i.val < 48
  · simp only [stackMap, dite_eq_left hlow, lowPort, ordinary,
      SubexpLayoutPorts.master_val] at hv
    omega
  by_cases hhigh : i.val < 60
  · have hm := SubexpLayoutPorts.master_injective alloc (by
      simpa only [stackMap, dite_eq_right hlow, dite_eq_left hhigh] using hi)
    rcases masterIndex_cases ⟨i.val - 48, by omega⟩ with ⟨k, hk⟩ | hk
    · exact hin k (hk.trans hm)
    · exact hout (hm ▸ hk)
  · simp only [stackMap, dite_eq_right hlow, dite_eq_right hhigh, lowPort, ordinary,
      SubexpLayoutPorts.master_val] at hv
    norm_num at hv
    omega

end SubexponentialSAT.SubexpMainPacking

end OAI.Algorithms
