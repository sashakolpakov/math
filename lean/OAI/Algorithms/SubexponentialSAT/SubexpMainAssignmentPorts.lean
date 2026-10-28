import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpAssignmentStagingCore
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts

namespace OAI.Algorithms

/-! Fixed injective port map for Main assignment staging. -/

namespace SubexponentialSAT.SubexpMainAssignment

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod Fin.ext_iff

def metadataIndex : Fin 4 → Fin 32 := ![21, 17, 16, 19]
def masterIndex : Fin 8 → Fin 32 := ![0, 2, 3, 4, 5, 6, 7, 8]
def targetIndex : Fin 3 → Fin 32 := ![2, 3, 4]
def writtenMasters : Finset (Fin 32) := {2, 3, 4, 5, 6, 7, 8}

theorem metadataIndex_injective : Function.Injective metadataIndex := by decide
theorem masterIndex_injective : Function.Injective masterIndex := by decide

def lowPort {es : ℕ} (alloc : Allocation es) (i : Fin 51) : Fin (totalStacks es) :=
  ordinary alloc ⟨i.val, by omega⟩

def inputPort {es : ℕ} (alloc : Allocation es) (i : Fin 5) : Fin (totalStacks es) :=
  if hi : i.val < 4 then persistent es (metadataIndex ⟨i.val, hi⟩) else master alloc 0

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 63) : Fin (totalStacks es) :=
  if hlo : i.val < 51 then lowPort alloc ⟨i.val, hlo⟩
  else if hmid : i.val < 55 then persistent es (metadataIndex ⟨i.val - 51, by omega⟩)
  else master alloc (masterIndex ⟨i.val - 55, by omega⟩)

theorem stackMap_of_low {es : ℕ} (alloc : Allocation es) (i : Fin 63)
    (hi : i.val < 51) : stackMap alloc i = lowPort alloc ⟨i.val, hi⟩ := by
  simp only [stackMap, dite_eq_left hi]

theorem stackMap_of_middle {es : ℕ} (alloc : Allocation es) (i : Fin 63)
    (hlo : ¬i.val < 51) (hmid : i.val < 55) :
    stackMap alloc i = persistent es (metadataIndex ⟨i.val - 51, by omega⟩) := by
  simp only [stackMap, dite_eq_right hlo, dite_eq_left hmid]

theorem stackMap_of_high {es : ℕ} (alloc : Allocation es) (i : Fin 63)
    (hlo : ¬i.val < 51) (hmid : ¬i.val < 55) :
    stackMap alloc i = master alloc (masterIndex ⟨i.val - 55, by omega⟩) := by
  simp only [stackMap, dite_eq_right hlo, dite_eq_right hmid]

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  have hcount := alloc.enough.trans alloc.within
  by_cases hi : i.val < 51 <;> by_cases hj : j.val < 51
  · have hv := congrArg Fin.val ((stackMap_of_low alloc i hi).symm.trans
      (h.trans (stackMap_of_low alloc j hj)))
    apply Fin.ext
    simpa only [lowPort, ordinary] using hv
  · by_cases hj' : j.val < 55
    · have hv := congrArg Fin.val ((stackMap_of_low alloc i hi).symm.trans
        (h.trans (stackMap_of_middle alloc j hj hj')))
      simp only [lowPort, ordinary, persistent, Fin.val_natAdd] at hv
      omega
    · have hv := congrArg Fin.val ((stackMap_of_low alloc i hi).symm.trans
        (h.trans (stackMap_of_high alloc j hj hj')))
      simp only [lowPort, ordinary, SubexpLayoutPorts.master_val] at hv
      omega
  · by_cases hi' : i.val < 55
    · have hv := congrArg Fin.val ((stackMap_of_middle alloc i hi hi').symm.trans
        (h.trans (stackMap_of_low alloc j hj)))
      simp only [lowPort, ordinary, persistent, Fin.val_natAdd] at hv
      omega
    · have hv := congrArg Fin.val ((stackMap_of_high alloc i hi hi').symm.trans
        (h.trans (stackMap_of_low alloc j hj)))
      simp only [lowPort, ordinary, SubexpLayoutPorts.master_val] at hv
      omega
  · by_cases hi' : i.val < 55 <;> by_cases hj' : j.val < 55
    · have he := persistent_injective es (by
        exact (stackMap_of_middle alloc i hi hi').symm.trans
          (h.trans (stackMap_of_middle alloc j hj hj')))
      have he' := congrArg (fun q : Fin 4 => q.val) (metadataIndex_injective he)
      apply Fin.ext
      dsimp only at he'
      omega
    · exact False.elim (SubexpLayoutPorts.master_ne_persistent alloc
        (masterIndex ⟨j.val - 55, by omega⟩)
        (metadataIndex ⟨i.val - 51, by omega⟩)
        ((stackMap_of_high alloc j hj hj').symm.trans
          (h.symm.trans (stackMap_of_middle alloc i hi hi'))))
    · exact False.elim (SubexpLayoutPorts.master_ne_persistent alloc
        (masterIndex ⟨i.val - 55, by omega⟩)
        (metadataIndex ⟨j.val - 51, by omega⟩)
        ((stackMap_of_high alloc i hi hi').symm.trans
          (h.trans (stackMap_of_middle alloc j hj hj'))))
    · have he := SubexpLayoutPorts.master_injective alloc (by
        exact (stackMap_of_high alloc i hi hi').symm.trans
          (h.trans (stackMap_of_high alloc j hj hj')))
      have he' := congrArg (fun q : Fin 8 => q.val) (masterIndex_injective he)
      apply Fin.ext
      dsimp only at he'
      omega

@[simp] theorem stackMap_low {es : ℕ} (alloc : Allocation es) (i : Fin 51) :
    stackMap alloc (i.castAdd 12) = lowPort alloc i := by
  simp only [stackMap, Fin.val_castAdd, dite_eq_left i.isLt]

@[simp] theorem stackMap_metadata {es : ℕ} (alloc : Allocation es) (i : Fin 4) :
    stackMap alloc (SubexpAssignmentSetup.source i) = persistent es (metadataIndex i) := by
  fin_cases i <;> simp [stackMap, SubexpAssignmentSetup.source, metadataIndex]

@[simp] theorem stackMap_input {es : ℕ} (alloc : Allocation es) (i : Fin 5) :
    stackMap alloc (SubexpAssignmentStaging.input i) = inputPort alloc i := by
  fin_cases i <;> simp [stackMap, SubexpAssignmentStaging.input, inputPort, metadataIndex, masterIndex]

@[simp] theorem stackMap_output {es : ℕ} (alloc : Allocation es) (i : Fin 3) :
    stackMap alloc (SubexpAssignmentStaging.outputTarget i) = master alloc (targetIndex i) := by
  fin_cases i <;> simp [stackMap, SubexpAssignmentStaging.outputTarget, masterIndex, targetIndex]

def headerIndex (i : Fin 4) : Fin 32 := ⟨5 + i.val, by omega⟩

@[simp] theorem stackMap_header {es : ℕ} (alloc : Allocation es) (i : Fin 4) :
    stackMap alloc (SubexpAssignmentStaging.headerTarget i) = master alloc (headerIndex i) := by
  fin_cases i <;> simp [stackMap, SubexpAssignmentStaging.headerTarget, masterIndex, headerIndex]

theorem stackMap_avoids_middle {es : ℕ} (alloc : Allocation es) (j : Fin (totalStacks es))
    (hlo : 51 ≤ j.val) (hhi : j.val < 640) : ¬ ∃ i, stackMap alloc i = j := by
  rintro ⟨i, hi⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hi
  by_cases hsmall : i.val < 51
  · simp only [stackMap, dite_eq_left hsmall, lowPort, ordinary] at hv
    omega
  by_cases hmid : i.val < 55
  · rw [stackMap_of_middle alloc i hsmall hmid] at hi
    have hv := congrArg Fin.val hi
    simp only [persistent, Fin.val_natAdd] at hv
    have := alloc.enough.trans alloc.within
    omega
  · rw [stackMap_of_high alloc i hsmall hmid] at hi
    have hv := congrArg Fin.val hi
    simp only [SubexpLayoutPorts.master_val] at hv
    omega

theorem stackMap_avoids_master {es : ℕ} (alloc : Allocation es) (j : Fin 32)
    (h0 : j ≠ 0) (hw : j ∉ writtenMasters) : ¬ ∃ i, stackMap alloc i = master alloc j := by
  rintro ⟨i, hi⟩
  by_cases hsmall : i.val < 51
  · have h := SubexpLayoutPorts.master_ne_low alloc j (lowPort alloc ⟨i.val, hsmall⟩)
      (by simp [lowPort, ordinary]; omega)
    apply h
    simpa only [stackMap, dite_eq_left hsmall] using hi.symm
  by_cases hmid : i.val < 55
  · have h := SubexpLayoutPorts.master_ne_persistent alloc j (metadataIndex ⟨i.val - 51, by omega⟩)
    apply h
    simpa only [stackMap, dite_eq_right hsmall, dite_eq_left hmid] using hi.symm
  · have he := SubexpLayoutPorts.master_injective alloc (by
      simpa only [stackMap, dite_eq_right hsmall, dite_eq_right hmid] using hi)
    have hm : ∀ k, masterIndex k = 0 ∨ masterIndex k ∈ writtenMasters := by decide
    rcases hm ⟨i.val - 55, by omega⟩ with h | h
    · exact h0 (he.symm.trans h)
    · exact hw (he ▸ h)


end SubexponentialSAT.SubexpMainAssignment

end OAI.Algorithms
