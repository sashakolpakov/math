import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.SheafComparison
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Finite -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Finite

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Finiteness of the actual rational singular homology in the CM setting -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The additive comparison for rational coefficients is automatically rational-linear. -/
def constantSheafSingularRationalEquiv (n : ℕ) :
    H^n(X; ℚ) ≃ₗ[ℚ] AlgebraicTopology.Singular.CohomologyTo.Cohomology ℚ ↧(ComplexPoint.Basic.ComplexSchemePoint X) n :=
  let e := SheafComparison.constantSheafSingularAddEquiv ℚ X n
  LinearEquiv.ofBijective e.toAddMonoidHom.toRatLinearMap e.bijective

omit [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
/-- The original rank-one product-of-number-fields model makes rational H¹ finite-dimensional. -/
theorem cmH1Data_finite (d : Definitions.CMH1Data X) : FiniteDimensional ℚ H^1(X; ℚ) :=
  FiniteDimensional.of_injective d.model.toLinearMap d.model.injective

/-- Finiteness transfers through the actual constant-sheaf/singular and universal-coefficient
comparisons. It concerns the original singular homology, without substituting a model for it. -/
theorem cmH1Data_singularHomology_finite (d : Definitions.CMH1Data X) :
    FiniteDimensional ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ ↧(ComplexPoint.Basic.ComplexSchemePoint X) 1) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let e := constantSheafSingularRationalEquiv X 1
  let := cmH1Data_finite X d
  have : FiniteDimensional ℚ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℚ Y 1) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  let u := AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℚ Y 1
  have : FiniteDimensional ℚ
      (Module.Dual ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y 1)) :=
    FiniteDimensional.of_injective u.symm.toLinearMap u.symm.injective
  exact (Module.finite_dual_iff ℚ).mp inferInstance

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Finite
