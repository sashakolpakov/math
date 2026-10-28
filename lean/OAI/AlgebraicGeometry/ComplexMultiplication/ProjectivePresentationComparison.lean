import OAI.AlgebraicGeometry.ComplexMultiplication.ProjectiveBaseChange
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Projective Presentation Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ProjectivePresentationComparison.ProjectiveCharts

noncomputable section

/-! # Comparing the two actual complex projective schemes

The older complex-coefficient Proj is the genuine base change of integral Proj,
which is the unchanged Paul-Lez projective-space definition. The isomorphism
respects the original morphisms to Spec ℂ.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

private def integralComplexCoefficients : ULift ℤ →+* ℂ :=
  (Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom

private instance : Algebra (ULift ℤ) ℂ := integralComplexCoefficients.toAlgebra

private theorem complexProjectiveSpace_isPullback (n : ℕ) :
    IsPullback (ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase ℂ n)
      (ProjectiveChartNaturality.ProjectiveCharts.projectiveCoefficientMap (ULift ℤ) ℂ integralComplexCoefficients n)
      (terminal.from (Spec (.of ℂ)))
      (terminal.from (ProjectiveChartSchemes.ProjectiveCharts.projectiveSpace (ULift ℤ) n)) := by
  let e : Spec (.of (ULift ℤ)) ≅ ⊤_ Scheme :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  refine (ProjectiveBaseChange.ProjectiveCharts.projectiveCoefficientMap_isPullback (ULift ℤ) ℂ n).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · simp
  · simp
    rfl
  · exact terminal.hom_ext _ _
  · exact terminal.hom_ext _ _

theorem degreeZeroConstants_complex_eq (n : ℕ) :
    CMProjectiveCharts.ProjectiveCharts.degreeZeroConstants ℂ n = Foundations.Scheme.ProjectiveSpace.degreeZeroConstants n := by
  apply RingEquiv.ext
  intro z
  apply Subtype.ext
  rfl

theorem projectiveSpaceToBase_complex_eq (n : ℕ) :
    ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase ℂ n = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  rw [ProjectiveChartSchemes.ProjectiveCharts.projectiveSpaceToBase, Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase, degreeZeroConstants_complex_eq]

/-- The actual complex-coefficient Proj and the actual Paul-Lez projective space are isomorphic. -/
def complexProjectiveSpaceIso (n : ℕ) :
    Foundations.Scheme.ProjectiveSpace.projectiveSpace n ≅ Foundations.ProjectiveSpaceIs.ProjectiveSpace (Fin (n + 1)) (Spec (.of ℂ)) :=
  (complexProjectiveSpace_isPullback n).isoPullback

/-- The projective scheme comparison retains the original coefficient-field structure map. -/
theorem complexProjectiveSpaceIso_over (n : ℕ) :
    (complexProjectiveSpaceIso n).hom ≫
      Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (n + 1)) (Spec (.of ℂ)) =
        Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  change (complexProjectiveSpace_isPullback n).isoPullback.hom ≫ pullback.fst _ _ = _
  rw [IsPullback.isoPullback_hom_fst]
  exact projectiveSpaceToBase_complex_eq n

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ProjectivePresentationComparison.ProjectiveCharts
