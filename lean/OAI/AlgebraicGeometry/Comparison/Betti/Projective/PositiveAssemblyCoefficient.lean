import OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveWeightCoefficient
import OAI.AlgebraicGeometry.Comparison.Betti.PositiveAnalyticMonomial

/-! # Positive Assembly Coefficient -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveAssemblyCoefficient.Dolbeault

noncomputable section

/-! Every original nonnegative Laurent zero-cycle assembly has the canonical analytic coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open scoped BigOperators

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace
attribute [local instance] SectorProperSupportContraction.Dolbeault.properSupportCoefficients_addCommGroup SectorProperSupportContraction.Dolbeault.properSupportCochains_addCommGroup

theorem projectiveLaurentZeroFromCoefficients_sum (n k : ℕ) (j : Fin (n + 1))
    (c : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ) → Γ(Spec (CommRingCat.of ℂ), ⊤)) :
    SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroFromCoefficients (R := ℂ) (k : ℤ) j c =
      ∑ e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ), PositiveWeightCoefficient.Dolbeault.projectiveNonnegativeWeightZeroCycle n k j e (c e) := by
  simp only [SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroFromCoefficients, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

theorem projectiveLaurentOriginalComparison_zero_nonnegative_assembly (n k : ℕ) (j : Fin (n + 1))
    (c : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ) → Γ(Spec (CommRingCat.of ℂ), ⊤)) :
    ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient n j (k : ℤ)
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (k : ℤ)).f 0
        (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroFromCoefficients (R := ℂ) (k : ℤ) j c).val) =
      PositiveAnalyticMonomial.Dolbeault.algebraicPositiveLaurentCoefficientEquiv (n + 1) k c := by
  let F : (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j (k : ℤ)).X 0 →+
      HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset (Fin (n + 1))) (k : ℤ) :=
    (ZeroCoefficientValues.Dolbeault.projectiveTwistZeroCoefficient n j (k : ℤ)).comp
      ((LaurentComplex.Dolbeault.projectiveLaurentOriginalComparison n j (k : ℤ)).f 0).hom
  let a := PositiveAnalyticMonomial.Dolbeault.algebraicPositiveLaurentCoefficientEquiv (n + 1) k c
  have hs := projectiveLaurentZeroFromCoefficients_sum n k j c
  have hv := map_sum (SheafCohomology.Projective.LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := ℂ) (σ := Fin (n + 1)) (k : ℤ)).subtype.toAddMonoidHom
    (fun e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ) => PositiveWeightCoefficient.Dolbeault.projectiveNonnegativeWeightZeroCycle n k j e (c e))
    Finset.univ
  have hs' := (congrArg Subtype.val hs).trans hv
  change F (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.laurentZeroFromCoefficients (R := ℂ) (k : ℤ) j c).val = a
  refine (congrArg F hs').trans ?_
  refine (map_sum F (fun e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ) =>
    ((PositiveWeightCoefficient.Dolbeault.projectiveNonnegativeWeightZeroCycle n k j e (c e)).val :
      (LaurentComplex.Dolbeault.projectiveAlgebraicLaurentCechComplex n j (k : ℤ)).X 0)) Finset.univ).trans ?_
  calc
    _ = ∑ e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ),
        PositiveAnalyticMonomial.Dolbeault.positiveAnalyticMonomial (n + 1) k e ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (c e)) := by
      apply Finset.sum_congr rfl
      intro e _
      exact PositiveWeightCoefficient.Dolbeault.projectiveLaurentOriginalComparison_zero_nonnegative_weight n k j e (c e)
    _ = ∑ e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin (n + 1)) (k : ℤ),
        PositiveAnalyticMonomial.Dolbeault.positiveAnalyticMonomial (n + 1) k e (PositiveAnalyticMonomial.Dolbeault.positiveAnalyticLaurentCoefficientEquiv (n + 1) k a e) := by
      apply Finset.sum_congr rfl
      intro e _
      exact congrArg (PositiveAnalyticMonomial.Dolbeault.positiveAnalyticMonomial (n + 1) k e)
        (PositiveAnalyticMonomial.Dolbeault.algebraicPositiveLaurentCoefficientEquiv_coefficient (n + 1) k c e).symm
    _ = a := PositiveAnalyticMonomial.Dolbeault.positiveAnalyticCoefficient_expansion (n + 1) k a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.PositiveAssemblyCoefficient.Dolbeault
