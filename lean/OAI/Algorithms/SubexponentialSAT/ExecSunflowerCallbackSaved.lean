import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallback

namespace OAI.Algorithms

/-! The materialized family and core remain paired with the first saved tuple. -/

namespace SubexponentialSAT.ExecSunflowerCallback

def Saved (F : Formula) (limit width size : List Bool) (d : Data) : Prop :=
  d.stacks 21 ≠ [] → ∃ mask words,
    d.stacks 21 = CandidatePrepareProgram.tupleCode (mask :: words) ∧
    accepted F mask limit width size words = true ∧
    d.stacks 13 = CandidatePrepareProgram.formulaCode
      (CandidatePrepareProgram.selected F words) ∧
    d.stacks 8 = CandidatePrepareProgram.clauseCode
      (CandidatePrepareProgram.core F mask words)

theorem saved_of_empty (F : Formula) (limit width size : List Bool) (d : Data)
    (h : d.stacks 21 = []) : Saved F limit width size d := by
  intro hn
  exact False.elim (hn h)

theorem saved_preserved (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d e : Data)
    (h : Saved F limit width size d)
    (ht : d.stacks 17 = CandidatePrepareProgram.tupleCode (mask :: words))
    (hs : e.stacks = outputStacks F mask limit width size words d) :
    Saved F limit width size e := by
  intro he
  by_cases hw : d.stacks 21 = []
  · have ha : accepted F mask limit width size words = true := by
      cases hac : accepted F mask limit width size words
      · have hz : e.stacks 21 = [] := by simp [hs, outputStacks, freshStacks, hw, hac]
        exact False.elim (he hz)
      · rfl
    refine ⟨mask, words, ?_, ha, ?_, ?_⟩
    · simp [hs, outputStacks, freshStacks, hw, ha, ht]
    · simp [hs, outputStacks, freshStacks, hw, ha]
    · simp [hs, outputStacks, freshStacks, hw, ha]
  · obtain ⟨oldMask, oldWords, htuple, ha, hG, hH⟩ := h hw
    exact ⟨oldMask, oldWords, by simpa [hs, outputStacks, hw] using htuple,
      ha, by simpa [hs, outputStacks, hw] using hG,
      by simpa [hs, outputStacks, hw] using hH⟩

/-- Once a witness exists, every materialized field is unchanged. -/
theorem all_stacks_preserved_after_success (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (d e : Data) (hw : d.stacks 21 ≠ [])
    (hs : e.stacks = outputStacks F mask limit width size words d) :
    e.stacks = d.stacks := by
  simpa only [outputStacks, ite_eq_right hw] using hs

end SubexponentialSAT.ExecSunflowerCallback

end OAI.Algorithms
