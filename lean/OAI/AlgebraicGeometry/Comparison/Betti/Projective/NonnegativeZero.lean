import OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveAssemblyCoefficient
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ZeroCycleModel
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ZeroCycles
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentHomology

/-! # Nonnegative Zero -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeZero.Dolbeault

noncomputable section

/-! The actual degree-zero comparison for nonnegative twists on positive-dimensional projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveHomology.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveLaurentOriginalComparison_zero_nonnegative_cycle (n k : ℕ) (j : Fin (n + 1))
    (z : SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 1)) (k : ℤ)) :
    ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient n j (k : ℤ)
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (k : ℤ)).f 0 z.val) =
    PositiveAnalyticMonomial.Dolbeault.algebraicPositiveLaurentCoefficientEquiv (n + 1) k (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroCoefficients (R := ℂ) (k : ℤ) j z) := by
  have h := PositiveAssemblyCoefficient.Dolbeault.projectiveLaurentOriginalComparison_zero_nonnegative_assembly n k j
    (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroCoefficients (R := ℂ) (k : ℤ) j z)
  have hz := SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroFrom_coefficients (R := ℂ) (k : ℤ) (Int.natCast_nonneg k) j z
  have hv := congrArg Subtype.val hz
  exact (congrArg (fun x => ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient n j (k : ℤ)
    ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (k : ℤ)).f 0 x)) hv).symm.trans h

theorem projectiveLaurentOriginalComparison_zero_nonnegative_bijective (n k : ℕ) (j : Fin (n + 2)) :
    Function.Bijective (AdditiveHomology.Cech.additiveZeroCycleMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (n + 1) j (k : ℤ))) := by
  let B := LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (n + 1) j (k : ℤ)
  let E := (ZeroCycleModel.Dolbeault.projectiveLaurentZeroCyclesEquiv (n + 1) j (k : ℤ)).trans
    (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroCyclesEquivCoefficients (R := ℂ) (k : ℤ) (Int.natCast_nonneg k) j).toAddEquiv
  let C := PositiveAnalyticMonomial.Dolbeault.algebraicPositiveLaurentCoefficientEquiv (n + 2) k
  let A := ProjectiveTwist.ZeroCycles.Dolbeault.projectiveTwistZeroCycleCoefficientEquiv n j (k : ℤ)
  let I := E.trans (C.trans A.symm)
  have he : ∀ z, A (AdditiveHomology.Cech.additiveZeroCycleMap B z) = C (E z) := by
    intro z
    exact projectiveLaurentOriginalComparison_zero_nonnegative_cycle (n + 1) k j
      (ZeroCycleModel.Dolbeault.projectiveLaurentZeroCyclesEquiv (n + 1) j (k : ℤ) z)
  have h : AdditiveHomology.Cech.additiveZeroCycleMap B = I.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro z
    apply A.injective
    exact (he z).trans (A.apply_symm_apply (C (E z))).symm
  rw [h]
  exact I.bijective

theorem projectiveLaurentOriginalComparison_zero_nonnegative_isIso (n k : ℕ) (j : Fin (n + 2)) :
    IsIso (homologyMap (LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison (n + 1) j (k : ℤ)) 0) :=
  AdditiveHomology.Cech.additiveHZeroMap_isIso_of_zeroCycles _ (projectiveLaurentOriginalComparison_zero_nonnegative_bijective n k j)

theorem projectiveOriginalComparison_zero_nonnegative_isIso (n k : ℕ) (j : Fin (n + 2)) :
    IsIso (homologyMap (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap (n + 1) j (k : ℤ)) 0) := by
  let := projectiveLaurentOriginalComparison_zero_nonnegative_isIso n k j
  exact LaurentHomology.Dolbeault.projectiveOriginalComparison_isIso_of_laurent (n + 1) j (k : ℤ) 0

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.NonnegativeZero.Dolbeault
