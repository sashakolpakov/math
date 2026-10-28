import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallbackSaved
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerSearchSpec

namespace OAI.Algorithms

/-! A saved concrete search result is a normalized finite sunflower witness. -/

namespace SubexponentialSAT.ExecSunflowerCallback

theorem accepted_eq_search_accept (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) :
    accepted F mask limit width size words =
      ExecSunflowerSearchSpec.accept F mask limit width size words := rfl

/-- This is the data contract consumed by the two-child constructor.  The
source, selected family, and core are the actual retained stack contents. -/
theorem saved_sound (F : Formula) (limit width size : List Bool) (d : Data)
    (h : Saved F limit width size d) (hne : d.stacks 21 ≠ [])
    (hF : (F.map ExecCNF.clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hlimit : BinaryArithmetic.toNat limit = F.length) :
    ∃ G : Formula, ∃ H : Clause,
      d.stacks 13 = CandidatePrepareProgram.formulaCode G ∧
      d.stacks 8 = CandidatePrepareProgram.clauseCode H ∧
      G ⊆ F ∧ (ExecCNF.clauseSet H).Nonempty ∧
      Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) ∧
      (ExecCNF.formulaSet G).card = BinaryArithmetic.toNat size ∧
      ∀ C ∈ ExecCNF.formulaSet G, C.card = BinaryArithmetic.toNat width := by
  obtain ⟨mask, words, _, ha, hG, hH⟩ := h hne
  rw [accepted_eq_search_accept] at ha
  obtain ⟨hsub, hfiltered, hcore, hflower, hcard⟩ :=
    ExecSunflowerSearchSpec.sound F mask limit width size words hF hC hlimit ha
  refine ⟨_, _, hG, hH, hsub, hcore, hflower, hcard, ?_⟩
  intro C hC
  exact (Finset.mem_filter.mp (hfiltered hC)).2

/-- The retained core is an ordered sublist of an actual input clause.  This
uses the mask construction itself, rather than inferring raw-list facts from
equality of finite sets. -/
theorem accepted_core_sublist (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (ha : accepted F mask limit width size words = true) :
    ∃ C ∈ F, (CandidatePrepareProgram.core F mask words).Sublist C := by
  obtain ⟨_, hanswer⟩ := Bool.and_eq_true_iff.mp ha
  have hcore := ((ExecSunflowerCandidateProgram.answer_true_iff _ _ width size).mp hanswer).2
  let G := CandidatePrepareProgram.selected F words
  have hG : G ≠ [] := by
    intro hnil
    apply hcore
    change CoreMaskProgram.select mask (G.headD []) = []
    simp [hnil, CoreMaskProgram.select]
  have hhead : G.headD [] ∈ G := by
    cases hlist : G with
    | nil => exact False.elim (hG hlist)
    | cons C Cs => simp
  exact ⟨G.headD [], ExecSunflowerSearchSpec.selected_mem_source F words hhead,
    CoreMaskProgram.select_sublist mask (G.headD [])⟩

theorem saved_sound_with_core_sublist (F : Formula) (limit width size : List Bool) (d : Data)
    (h : Saved F limit width size d) (hne : d.stacks 21 ≠ [])
    (hF : (F.map ExecCNF.clauseSet).Nodup) (hC : ∀ C ∈ F, C.Nodup)
    (hlimit : BinaryArithmetic.toNat limit = F.length) :
    ∃ G : Formula, ∃ H : Clause,
      d.stacks 13 = CandidatePrepareProgram.formulaCode G ∧
      d.stacks 8 = CandidatePrepareProgram.clauseCode H ∧
      G ⊆ F ∧ H.Nodup ∧ (∃ C ∈ F, H.Sublist C) ∧
      (ExecCNF.clauseSet H).Nonempty ∧
      Sunflower.IsSunflowerWithCore (ExecCNF.formulaSet G) (ExecCNF.clauseSet H) ∧
      (ExecCNF.formulaSet G).card = BinaryArithmetic.toNat size ∧
      ∀ C ∈ ExecCNF.formulaSet G, C.card = BinaryArithmetic.toNat width := by
  obtain ⟨mask, words, _, ha, hG, hH⟩ := h hne
  obtain ⟨C, hCF, hHC⟩ := accepted_core_sublist F mask limit width size words ha
  rw [accepted_eq_search_accept] at ha
  obtain ⟨hsub, hfiltered, hcore, hflower, hcard⟩ :=
    ExecSunflowerSearchSpec.sound F mask limit width size words hF hC hlimit ha
  refine ⟨_, _, hG, hH, hsub, hHC.nodup (hC C hCF), ⟨C, hCF, hHC⟩,
    hcore, hflower, hcard, ?_⟩
  intro D hD
  exact (Finset.mem_filter.mp (hfiltered hD)).2

end SubexponentialSAT.ExecSunflowerCallback

end OAI.Algorithms
