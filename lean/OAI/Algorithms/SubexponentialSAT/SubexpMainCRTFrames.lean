import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRT

namespace OAI.Algorithms

/-! Complete persistent and protected-bank frames for the concrete CRT
phase. Only persistent10 is written; context words are copied before the
controller runs. The five final scratch clears remain below both banks. -/

namespace SubexponentialSAT.SubexpMainCRT

open BitProgram StructuredCalls SubexpMainProgram

theorem highPort_persistent_cases {es : ℕ} (alloc : Allocation es)
    (j : Fin 10) (i : Fin 32) (h : highPort alloc j = persistent es i) :
    i = 10 ∨ ∃ k : Fin 7, inputIndex k = i := by
  fin_cases j
  · exact Or.inr ⟨0, persistent_injective es h⟩
  · exact Or.inr ⟨1, persistent_injective es h⟩
  · exact Or.inr ⟨2, persistent_injective es h⟩
  · exact Or.inr ⟨3, persistent_injective es h⟩
  · exact Or.inr ⟨4, persistent_injective es h⟩
  · exact Or.inr ⟨5, persistent_injective es h⟩
  · exact Or.inr ⟨6, persistent_injective es h⟩
  · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
    have hb := alloc.enough.trans alloc.within
    change 256 = workStacks es + i.val at hv
    omega
  · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
    have hb := alloc.enough.trans alloc.within
    change 265 = workStacks es + i.val at hv
    omega
  · exact Or.inl (persistent_injective es h).symm

theorem stackMap_persistent_cases {es : ℕ} (alloc : Allocation es)
    (j : Fin 330) (i : Fin 32) (h : stackMap alloc j = persistent es i) :
    i = 10 ∨ ∃ k : Fin 7, inputIndex k = i := by
  by_cases hj : (permutation j).val < 320
  · have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
    have hb := alloc.enough.trans alloc.within
    simp only [stackMap, baseMap, dite_eq_left hj, ordinary, persistent, Fin.val_natAdd] at hv
    omega
  · exact highPort_persistent_cases alloc _ i (by
      simpa only [stackMap, baseMap, dite_eq_right hj] using h)

/-- The exact contents of all persistent words other than the returned
quartet survive the full preparation, controller, and scratch epilogue. -/
theorem phase_persistent_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin 32) (hi : i ≠ 10) :
    (finalData alloc ((crt er alloc).install (preparedData alloc a) out)).stacks
      (persistent es i) = a.stacks (persistent es i) := by
  classical
  by_cases hin : ∃ k : Fin 7, inputIndex k = i
  · obtain ⟨k, rfl⟩ := hin
    exact phase_input alloc a out k
  have hmap : ¬ ∃ j, stackMap alloc j = persistent es i := by
    rintro ⟨j, hj⟩
    exact (stackMap_persistent_cases alloc j i hj).elim hi hin
  have hp : (preparedData alloc a).stacks (persistent es i) = a.stacks (persistent es i) :=
    embedState_stack_frame _ _ _ _ _ hmap
  have hc : ((crt er alloc).install (preparedData alloc a) out).stacks (persistent es i) =
      (preparedData alloc a).stacks (persistent es i) := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    exact hmap ⟨j.castAdd 10, hj⟩
  have hb := alloc.enough.trans alloc.within
  rw [finalData_high_frame alloc _ _ (by simp only [persistent, Fin.val_natAdd]; omega), hc, hp]

theorem stackMap_avoids_threshold {es : ℕ} (alloc : Allocation es)
    (i : Fin (totalStacks es)) (hlo : alloc.ordinaryCount ≤ i.val)
    (hhi : i.val < workStacks es) : ¬ ∃ j, stackMap alloc j = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  have hb := alloc.enough
  by_cases hp : (permutation j).val < 320
  · simp only [stackMap, baseMap, dite_eq_left hp, ordinary] at hv
    omega
  · have hr := highPort_range alloc ⟨(permutation j).val - 320, by
      have := (permutation j).isLt
      omega⟩
    simp only [stackMap, baseMap, dite_eq_right hp] at hv
    omega

theorem phase_threshold_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : StructuredProgram.State 16 320) (i : Fin (totalStacks es))
    (hlo : alloc.ordinaryCount ≤ i.val) (hhi : i.val < workStacks es) :
    (finalData alloc ((crt er alloc).install (preparedData alloc a) out)).stacks i = a.stacks i := by
  have hm := stackMap_avoids_threshold alloc i hlo hhi
  have hp : (preparedData alloc a).stacks i = a.stacks i :=
    embedState_stack_frame _ _ _ _ _ hm
  have hc : ((crt er alloc).install (preparedData alloc a) out).stacks i =
      (preparedData alloc a).stacks i := by
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    exact hm ⟨j.castAdd 10, hj⟩
  have hb := alloc.enough
  rw [finalData_high_frame alloc _ _ (by omega), hc, hp]

end SubexponentialSAT.SubexpMainCRT

end OAI.Algorithms
