import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchSearch
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchFraming
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorageBounds

namespace OAI.Algorithms

/-! Serialize the actual selected basis and clear the complete search bank. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

theorem searchWork_mem (j : Fin 128) :
    j ∈ searchWork ↔ (65 ≤ j.val ∧ j.val < 107) ∨ j = 124 := by
  simp only [searchWork, List.mem_append, List.mem_ofFn, List.mem_singleton]
  constructor
  · rintro (⟨i, rfl⟩ | rfl)
    · left
      simp only [searchPorts, Fin.val_mk]
      omega
    · exact Or.inr rfl
  · rintro (⟨hl, hu⟩ | rfl)
    · left
      refine ⟨⟨j.val - 65, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [searchPorts, Fin.val_mk]
      omega
    · exact Or.inr rfl

@[simp] theorem searchWork_length : searchWork.length = 43 := by simp [searchWork]

def finishSearch : Code := .seq emitResult
  (.seq (clearMany searchWork) (TupleProgram.pushConst 118 0 true))

def finishedSearch (a : Data) : Data :=
  TupleProgram.pushedState 118 0 true (clearManyState searchWork (emittedResult a))

def finishSearchCost (a : Data) : ℕ :=
  36 * ((a.stacks 123).length + (a.stacks 73).length + (a.stacks 106).length) + 85 +
    clearManyCost searchWork (emittedResult a) + 2

theorem finishSearch_eval (a : Data) (h0 : a.stacks 0 = [])
    (h125 : a.stacks 125 = []) (h126 : a.stacks 126 = []) :
    Eval finishSearch (finishSearchCost a) a (finishedSearch a) := by
  have h0 := emitResult_eval a h0 h125 h126
  have h1 := clearMany_eval searchWork (emittedResult a)
  have h2 := TupleProgram.pushConst_eval (118 : Fin 128) (0 : Fin 32) true
    (clearManyState searchWork (emittedResult a))
  have h : Eval finishSearch
      (36 * ((a.stacks 123).length + (a.stacks 73).length + (a.stacks 106).length) + 85 +
        (clearManyCost searchWork (emittedResult a) + 2)) a (finishedSearch a) :=
    h0.seq (h1.seq h2)
  simpa only [finishSearchCost, Nat.add_assoc] using h

def finishedSearchStacks (a : Data) (j : Fin 128) : Word :=
  if j = 118 then true :: a.stacks 118 else
  if j = 122 then
    (true :: Encoding.frame (resultPayload (a.stacks 123) (a.stacks 73) (a.stacks 106))).reverse ++
      a.stacks 122 else
  if j ∈ searchWork ∨ j = 123 then [] else a.stacks j

theorem finishedSearch_stacks (a : Data) (h126 : a.stacks 126 = []) :
    (finishedSearch a).stacks = finishedSearchStacks a := by
  funext j
  change (Function.update (clearManyState searchWork (emittedResult a)).stacks 118
    (true :: (clearManyState searchWork (emittedResult a)).stacks 118)) j = _
  have h118 : (118 : Fin 128) ∉ searchWork := by rw [searchWork_mem]; decide
  have h122 : (122 : Fin 128) ∉ searchWork := by rw [searchWork_mem]; decide
  have h123 : (123 : Fin 128) ∉ searchWork := by rw [searchWork_mem]; decide
  by_cases hj118 : j = 118
  · subst j
    simp only [Function.update_self, clearMany_stacks, ite_eq_right h118]
    rw [emittedResult_frame a 118 (by decide) (by decide) (by decide) (by decide) h126]
    simp [finishedSearchStacks]
  by_cases hj122 : j = 122
  · subst j
    simp only [Function.update_of_ne (by decide : (122 : Fin 128) ≠ 118),
      clearMany_stacks, ite_eq_right h122]
    rw [emittedResult_output a h126]
    simp [finishedSearchStacks]
  rw [Function.update_of_ne hj118, clearMany_stacks]
  by_cases hjwork : j ∈ searchWork
  · simp [finishedSearchStacks, hj118, hj122, hjwork]
  by_cases hj123 : j = 123
  · subst j
    simp only [ite_eq_right h123]
    rw [(emittedResult_sources a).2.2]
    simp [finishedSearchStacks, h123]
  have hj73 : j ≠ 73 := by
    intro he
    subst j
    exact hjwork ((searchWork_mem 73).mpr (by decide))
  have hj106 : j ≠ 106 := by
    intro he
    subst j
    exact hjwork ((searchWork_mem 106).mpr (by decide))
  simp only [ite_eq_right hjwork]
  rw [emittedResult_frame a j hj123 hj73 hj106 hj122 h126]
  simp [finishedSearchStacks, hj118, hj122, hjwork, hj123]

theorem finishedSearch_register_frame (a : Data) (j : Fin 32) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (finishedSearch a).regs j = a.regs j := by
  change (Function.update (clearManyState searchWork (emittedResult a)).regs 0 true) j = _
  rw [Function.update_of_ne h0, clearMany_register_frame _ _ j h0 h1]
  exact emittedResult_registers a j h0 h1

/-- The search bank is fully restored while one chosen payload is appended
to the reversed record accumulator and the color cursor is incremented. -/
theorem finishedSearch_frame (base a : Data) (N square d C : Word)
    (hbase : ∀ j : Fin 128, j.val < 107 ∨ j = 123 ∨ j = 124 → base.stacks j = [])
    (hlow : ∀ j : Fin 128, j.val < 65 → a.stacks j = [])
    (hhigh : ∀ j : Fin 128, 107 ≤ j.val → a.stacks j =
      Function.update (Function.update base.stacks 123 N) 124 square j)
    (hd : a.stacks 73 = d) (hC : a.stacks 106 = C) (h126 : a.stacks 126 = []) :
    (finishedSearch a).stacks =
      Function.update (Function.update base.stacks 122
        ((true :: Encoding.frame (resultPayload N d C)).reverse ++ base.stacks 122))
        118 (true :: base.stacks 118) := by
  have hN : a.stacks 123 = N := by simpa using hhigh 123 (by decide)
  have h118 : a.stacks 118 = base.stacks 118 := by simpa using hhigh 118 (by decide)
  have h122 : a.stacks 122 = base.stacks 122 := by simpa using hhigh 122 (by decide)
  rw [finishedSearch_stacks a h126]
  funext j
  by_cases hj118 : j = 118
  · subst j
    simp [finishedSearchStacks, h118]
  by_cases hj122 : j = 122
  · subst j
    simp [finishedSearchStacks, hN, hd, hC, h122]
  simp only [Function.update_of_ne hj118, Function.update_of_ne hj122]
  by_cases hw : j ∈ searchWork ∨ j = 123
  · have hz : base.stacks j = [] := by
      rcases hw with hw | rfl
      · rcases (searchWork_mem j).mp hw with hw | rfl
        · exact hbase j (Or.inl hw.2)
        · exact hbase 124 (Or.inr (Or.inr rfl))
      · exact hbase 123 (Or.inr (Or.inl rfl))
    simp [finishedSearchStacks, hj118, hj122, hw, hz]
  have hnotwork : j ∉ searchWork := fun h => hw (Or.inl h)
  have h123 : j ≠ 123 := fun h => hw (Or.inr h)
  have h124 : j ≠ 124 := by
    intro h
    exact hnotwork ((searchWork_mem j).mpr (Or.inr h))
  by_cases hlt : j.val < 65
  · simp [finishedSearchStacks, hj118, hj122, hw, hlow j hlt, hbase j (Or.inl (by omega))]
  have hge : 107 ≤ j.val := by
    by_contra hn
    exact hnotwork ((searchWork_mem j).mpr (Or.inl ⟨by omega, by omega⟩))
  have hh : a.stacks j = base.stacks j := by simpa [h123, h124] using hhigh j hge
  simp [finishedSearchStacks, hj118, hj122, hw, hh]

theorem finishSearchCost_le (a : Data) (B : ℕ) (h126 : a.stacks 126 = [])
    (hwork : ∀ j ∈ searchWork, (a.stacks j).length ≤ B)
    (hN : (a.stacks 123).length ≤ B)
    (hd : (a.stacks 73).length ≤ B) (hC : (a.stacks 106).length ≤ B) :
    finishSearchCost a ≤ 200 * (B + 2) := by
  have hc : ∀ j ∈ searchWork, ((emittedResult a).stacks j).length ≤ B := by
    intro j hj
    by_cases h73 : j = 73
    · subst j
      rw [(emittedResult_sources a).2.1]
      simp
    by_cases h106 : j = 106
    · subst j
      rw [(emittedResult_sources a).1]
      simp
    have h123 : j ≠ 123 := by
      intro he
      subst j
      exact (show (123 : Fin 128) ∉ searchWork from by rw [searchWork_mem]; decide) hj
    have h122 : j ≠ 122 := by
      intro he
      subst j
      exact (show (122 : Fin 128) ∉ searchWork from by rw [searchWork_mem]; decide) hj
    rw [emittedResult_frame a j h123 h73 h106 h122 h126]
    exact hwork j hj
  have hclear := clearManyCost_le searchWork (emittedResult a) B hc
  rw [searchWork_length] at hclear
  dsimp only [finishSearchCost]
  omega

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
