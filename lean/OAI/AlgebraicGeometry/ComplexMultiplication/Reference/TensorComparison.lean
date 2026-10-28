import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RationalCoefficientComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.FiniteComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange

/-! # Tensor Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.TensorComparison

noncomputable section

/-! # The exact original tensor comparison is the canonical Betti comparison -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The original rational de Rham map retains the actual rational coefficient inclusion. -/
theorem fieldToDeRham_schemeBetti (n : ℕ)
    (z : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n) :
    ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n z) =
      FiniteComparison.complexConstantSheafDeRhamLinearEquiv X n
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
          (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology
            (Betti.Scheme.schemePointSpace X) n z)) := by
  let cC := ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n
  let dC := ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
  have hc := RationalCoefficientComparison.schemeConstantCohomologyBridgeEquiv_rational_coefficient X n z
  have hi : cC.symm (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology
        (Betti.Scheme.schemePointSpace X) n z)) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt ℚ X) n
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n z)) :=
    (congrArg cC.symm hc).trans (cC.symm_apply_apply _)
  apply dC.symm.injective
  change dC.symm (ComplexPoint.Basic.ComplexSchemePoint.fieldToDeRhamCohomologyLinear ℚ X n
      (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X n z)) =
    dC.symm (dC (cC.symm (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology
        (Betti.Scheme.schemePointSpace X) n z))))
  exact (CMComparisonTo.complexComparison_symm_rational X n _).trans
    (hi.symm.trans (dC.symm_apply_apply _).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The map in unchanged `CM.lean` agrees with canonical complexification on every tensor. -/
theorem h1Comparison_schemeBetti
    (z : ℂ ⊗[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1) :
    Definitions.h1Comparison X ((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap.baseChange ℂ z) =
      FiniteComparison.complexConstantSheafDeRhamLinearEquiv X 1
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1
          (CohomologyBaseChange.CM.singularCohomologyComplexification
            (Betti.Scheme.schemePointSpace X) 1 z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    rw [LinearMap.baseChange_tmul, CMComparisonTo.h1Comparison_tmul,
      CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    let w : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X 1 :=
      AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X) 1 v
    let e := BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1
    let d := FiniteComparison.complexConstantSheafDeRhamLinearEquiv X 1
    exact (congrArg (c • ·) (fieldToDeRham_schemeBetti X 1 v)).trans
      ((d.map_smul c (e w)).symm.trans
        (congrArg d (e.map_smul c w).symm))
  | add x y hx hy => simp only [map_add, hx, hy]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.TensorComparison
