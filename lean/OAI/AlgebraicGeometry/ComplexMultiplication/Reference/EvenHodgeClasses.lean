import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalHodgePurity
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientComparison

/-! # Even Hodge Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The exact original rational Hodge classes map to the geometric CM theorem's classes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

/-- Equality of degree indices transports only the same original cohomology object. -/
def originalCohomologyDegreeEquiv {n m : ℕ} (h : n = m) :
    H^n(X; ℚ) ≃ₗ[ℚ] H^m(X; ℚ) := by
  subst m
  exact LinearEquiv.refl ℚ _

/-- The actual geometric comparison in the two literal spellings of the even degree. -/
def originalEvenBettiBridge (p : ℕ) :
    (V).rationalCohomology (p + p) ≃ₗ[ℚ] H^(2 * p)(X; ℚ) :=
  (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X (p + p)).trans
    (originalCohomologyDegreeEquiv X (two_mul p).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient inclusion commutes with the original full de Rham comparison in every degree. -/
theorem nativeRationalCoefficient_originalDeRham (n : ℕ)
    (a : (V).rationalCohomology n) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
          ((V).rationalCohomologyInclusion n a))) =
      ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n a) := by
  change ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
    ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
      (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology
          (Betti.Scheme.schemePointSpace X) n a))) = _
  rw [RationalCoefficientComparison.schemeConstantCohomologyBridgeEquiv_rational_coefficient,
    AddEquiv.symm_apply_apply, ← CMComparisonTo.complexComparison_symm_rational,
    AddEquiv.apply_symm_apply]

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The first original Hodge filtration is retained under literal degree transport. -/
theorem originalHodgeClass_degree_firstFiltration (p : ℕ) {n : ℕ} (h : n = 2 * p)
    (a : H^n(X; ℚ)) (ha : originalCohomologyDegreeEquiv X h a ∈ Hdg^p(X; ℚ)) :
    ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n a ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p (n : ℤ) := by
  subst n
  exact ha.1

set_option backward.isDefEq.respectTransparency false in
/-- Every original challenge Hodge class has the same genuine native rational Hodge type. -/
theorem originalHodgeClass_native (p : ℕ) (a : H^(2 * p)(X; ℚ))
    (ha : a ∈ Hdg^p(X; ℚ)) :
    (V).IsRationalHodgeClass p ((originalEvenBettiBridge X p).symm a) := by
  let b := (originalEvenBettiBridge X p).symm a
  have hb : originalEvenBettiBridge X p b = a :=
    (originalEvenBettiBridge X p).apply_symm_apply a
  apply RationalHodgePurity.originalRationalFiltered_implies_nativeHodge X p b
  rw [nativeRationalCoefficient_originalDeRham]
  apply originalHodgeClass_degree_firstFiltration X p (two_mul p).symm
  change originalEvenBettiBridge X p b ∈ Hdg^p(X; ℚ)
  rwa [hb]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.EvenHodgeClasses
