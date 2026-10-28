import OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner

/-! # Complex Operator Lift -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions

noncomputable section

/-! A genuine real operator commuting with complex scalars has a complex
linear realization; its real Hilbert adjoint also commutes with complex scalars. -/

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [InnerProductSpace ℝ G]
  [IsScalarTower ℝ ℂ G]

def complexOperatorLift (A : F →L[ℝ] G) (hA : ∀ (c : ℂ) (u : F), A (c • u) = c • A u) : F →L[ℂ] G :=
  { toLinearMap := { toFun := A, map_add' := A.map_add, map_smul' := hA }
    cont := A.continuous }

theorem complexOperatorLift_restrict (A : F →L[ℝ] G)
    (hA : ∀ (c : ℂ) (u : F), A (c • u) = c • A u) :
    (complexOperatorLift A hA).restrictScalars ℝ = A := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem real_adjoint_complex_smul [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (hA : ∀ (c : ℂ) (u : F), A (c • u) = c • A u)
    (c : ℂ) (u : G) : A.adjoint (c • u) = c • A.adjoint u := by
  rw [← complexOperatorLift_restrict A hA, CompatibleRealInner.Constructions.compatible_adjoint_restrictScalars]
  exact (complexOperatorLift A hA).adjoint.map_smul c u

end

end OAI.Analysis.HodgeTheory.Decomposition.ComplexOperatorLift.Constructions
