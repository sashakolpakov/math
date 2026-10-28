import OAI.Analysis.HodgeTheory.Decomposition.Core

/-! # Degree One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DegreeOne.BettiHodge

noncomputable section

/-! The degree-one Hodge sum has precisely its two possible bidegrees. -/

open OAI.Analysis.HodgeTheory.Decomposition.Core.Constructions

theorem degreeOne_hodgeSum (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (hsplit : DirectSum.IsInternal (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X 1)) (p : ℤ) :
    (⨆ (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1) (_ : p ≤ (i.val.1 : ℤ)), Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X 1 i) =
      if p ≤ 0 then ⊤ else if p = 1 then X.pureBettiSubspace 1 0 else ⊥ := by
  by_cases hp : p ≤ 0
  · have hall : ∀ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1, p ≤ (i.val.1 : ℤ) := by
      intro i
      omega
    simpa only [hall, iSup_pos, ite_eq_left hp] using
      hsplit.submodule_iSup_eq_top
  · rw [ite_eq_right hp]
    by_cases hp1 : p = 1
    · rw [ite_eq_left hp1]
      subst p
      apply le_antisymm
      · refine iSup_le (fun i => iSup_le (fun hi => ?_))
        have hi' : i = ⟨(1, 0), rfl⟩ := by
          apply Subtype.ext
          apply Prod.ext
          · have := i.property
            dsimp at *
            omega
          · have := i.property
            dsimp at *
            omega
        subst i
        exact le_rfl
      · exact le_iSup_of_le (⟨(1, 0), rfl⟩ : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1)
          (le_iSup_of_le (show (1 : ℤ) ≤ 1 from le_rfl) le_rfl)
    · have hnone : ∀ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1, ¬ p ≤ (i.val.1 : ℤ) := by
        intro i
        have := i.property
        omega
      simp [hnone, hp1]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DegreeOne.BettiHodge
