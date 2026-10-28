import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChangeFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Algebra.Homology.Notation

/-! # Finite Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FiniteComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The original comparison is bijective in the original CM-data setting -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular
open scoped TensorProduct

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The original complex constant-sheaf/de Rham comparison is complex-linear. -/
def complexConstantSheafDeRhamLinearEquiv (n : ℕ) : H^n(X; ℂ) ≃ₗ[ℂ] H_dR^n(X) :=
  { (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm.trans
      (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n) with
    map_smul' := by
      intro c z
      change ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X n
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm (c • z)) = _
      rw [ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology_symm_smul]
      exact CMComparisonTo.complexComparison_scalar X n c _ }

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- In the original CM-data setting, genuine holomorphic de Rham H¹ is finite-dimensional. -/
theorem cmH1Data_deRham_finite (d : Definitions.CMH1Data X) : FiniteDimensional ℂ H_dR^1(X) := by
  let e := (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X 1).trans
    (complexConstantSheafDeRhamLinearEquiv X 1)
  let := SingularBaseChangeFinite.cmH1Data_complexSingularCohomology_finite X d
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

/-- The de Rham dimension equals the original rational H¹ dimension, without replacing
either cohomology group by the supplied rank-one model. -/
theorem cmH1Data_deRham_finrank (d : Definitions.CMH1Data X) :
    Module.finrank ℂ H_dR^1(X) = Module.finrank ℚ H^1(X; ℚ) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let e := (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X 1).trans
    (complexConstantSheafDeRhamLinearEquiv X 1)
  let := Coefficient.Finite.cmH1Data_singularHomology_finite X d
  let := SingularBaseChangeFinite.rationalComplexSingularHomology_finite Y 1
  calc
    _ = Module.finrank ℂ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℂ Y 1) := e.symm.finrank_eq
    _ = Module.finrank ℂ (Module.Dual ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y 1)) :=
      (AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℂ Y 1).finrank_eq
    _ = Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y 1) := Subspace.dual_finrank_eq
    _ = Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y 1) := SingularBaseChangeFinite.rationalComplexSingularHomology_finrank Y 1
    _ = Module.finrank ℚ (Module.Dual ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y 1)) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℚ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℚ Y 1) :=
      (AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℚ Y 1).symm.finrank_eq
    _ = Module.finrank ℚ H^1(X; ℚ) := (Coefficient.Finite.constantSheafSingularRationalEquiv X 1).symm.finrank_eq

/-- The specific map defined in `CM.lean` is bijective when the original CM data are supplied.
This theorem does not assert finite-dimensionality for every abelian variety. -/
theorem h1Comparison_bijective_of_cmH1Data (d : Definitions.CMH1Data X) :
    Function.Bijective (Definitions.h1Comparison X) := by
  let := Coefficient.Finite.cmH1Data_finite X d
  let := cmH1Data_deRham_finite X d
  have hdim : Module.finrank ℂ (ℂ ⊗[ℚ] H^1(X; ℚ)) = Module.finrank ℂ H_dR^1(X) :=
    Module.finrank_baseChange.trans (cmH1Data_deRham_finrank X d).symm
  exact ⟨CMComparisonTo.h1Comparison_injective X,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := CMComparisonTo.h1ComparisonComplex X)).mp (CMComparisonTo.h1Comparison_injective X)⟩

/-- The same original comparison with its proved inverse in the original CM-data setting. -/
def h1ComparisonLinearEquivOfCMH1Data (d : Definitions.CMH1Data X) :
    ℂ ⊗[ℚ] H^1(X; ℚ) ≃ₗ[ℂ] H_dR^1(X) :=
  LinearEquiv.ofBijective (CMComparisonTo.h1ComparisonComplex X) (h1Comparison_bijective_of_cmH1Data X d)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FiniteComparison
