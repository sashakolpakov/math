import OAI.AlgebraicGeometry.ComplexMultiplication.CMCompactManifold
import OAI.AlgebraicGeometry.ComplexMultiplication.FiniteComparison
import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveParacompact
import OAI.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import OAI.AlgebraicGeometry.Smooth.Equidimensional
import OAI.Algebra.Homology.Notation

/-! # Bare Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.BareComparison

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The original comparison without a CM finiteness hypothesis

The compact complex manifold here is the original space `ComplexPoint X`, with its
algebraic coordinate atlas. Cap duality makes its actual singular homology finite.
This proves bijectivity of the map in `CM.lean` before any CM data are supplied.
-/

open _root_.CategoryTheory OAI.AlgebraicTopology.Singular _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoint _root_.TopologicalSpace
open scoped TensorProduct

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

-- The older library has another topology on the same point carrier. Keep the original atlas.
local instance CMBareComparison.localInstance1 : TopologicalSpace (ComplexPoint.Basic.ComplexSchemePoint X) := ComplexPoint.Basic.Point.analyticTopology

/-- Actual rational singular homology of the original smooth projective variety is finite. -/
theorem rationalSingularHomology_finite (n : ℕ) :
    FiniteDimensional ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ ↧(ComplexPoint.Basic.ComplexSchemePoint X) n) :=
  CMCompactManifold.CompactManifoldFiniteness.rational_singularHomology_finite
    (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (M := ComplexPoint.Basic.ComplexSchemePoint X) n

/-- The original rational constant-sheaf cohomology is finite in every degree. -/
theorem rationalCohomology_finite (n : ℕ) : FiniteDimensional ℚ H^n(X; ℚ) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let := rationalSingularHomology_finite X n
  let e := (Coefficient.Finite.constantSheafSingularRationalEquiv X n).trans
    (AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℚ Y n)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Actual complex singular cohomology is finite in every degree. -/
theorem complexSingularCohomology_finite (n : ℕ) :
    FiniteDimensional ℂ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℂ ↧(ComplexPoint.Basic.ComplexSchemePoint X) n) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let := rationalSingularHomology_finite X n
  let := SingularBaseChangeFinite.rationalComplexSingularHomology_finite Y n
  let e := AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℂ Y n
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Genuine holomorphic de Rham cohomology is finite, without CM data. -/
theorem deRhamCohomology_finite (n : ℕ) : FiniteDimensional ℂ H_dR^n(X) := by
  let e := (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n).trans
    (FiniteComparison.complexConstantSheafDeRhamLinearEquiv X n)
  let := complexSingularCohomology_finite X n
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

/-- The dimensions of the original rational and holomorphic de Rham theories agree. -/
theorem deRhamCohomology_finrank (n : ℕ) :
    Module.finrank ℂ H_dR^n(X) = Module.finrank ℚ H^n(X; ℚ) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let e := (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℂ X n).trans
    (FiniteComparison.complexConstantSheafDeRhamLinearEquiv X n)
  let := rationalSingularHomology_finite X n
  let := SingularBaseChangeFinite.rationalComplexSingularHomology_finite Y n
  calc
    _ = Module.finrank ℂ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℂ Y n) := e.symm.finrank_eq
    _ = Module.finrank ℂ (Module.Dual ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y n)) :=
      (AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℂ Y n).finrank_eq
    _ = Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y n) := Subspace.dual_finrank_eq
    _ = Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n) := SingularBaseChangeFinite.rationalComplexSingularHomology_finrank Y n
    _ = Module.finrank ℚ (Module.Dual ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℚ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℚ Y n) :=
      (AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℚ Y n).symm.finrank_eq
    _ = Module.finrank ℚ H^n(X; ℚ) := (Coefficient.Finite.constantSheafSingularRationalEquiv X n).symm.finrank_eq

/-- The specific comparison in `CM.lean` is bijective under the original geometry alone. -/
theorem h1Comparison_bijective : Function.Bijective (Definitions.h1Comparison X) := by
  let := rationalCohomology_finite X 1
  let := deRhamCohomology_finite X 1
  have hdim : Module.finrank ℂ (ℂ ⊗[ℚ] H^1(X; ℚ)) = Module.finrank ℂ H_dR^1(X) :=
    Module.finrank_baseChange.trans (deRhamCohomology_finrank X 1).symm
  exact ⟨CMComparisonTo.h1Comparison_injective X,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := CMComparisonTo.h1ComparisonComplex X)).mp (CMComparisonTo.h1Comparison_injective X)⟩

/-- The original complex-linear comparison equipped with its proved inverse. -/
def h1ComparisonLinearEquiv : ℂ ⊗[ℚ] H^1(X; ℚ) ≃ₗ[ℂ] H_dR^1(X) :=
  LinearEquiv.ofBijective (CMComparisonTo.h1ComparisonComplex X) (h1Comparison_bijective X)

/-- The equivalence's underlying rational-linear map is literally the original map. -/
theorem h1ComparisonLinearEquiv_restrictScalars :
    (h1ComparisonLinearEquiv X).toLinearMap.restrictScalars ℚ = Definitions.h1Comparison X := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.BareComparison
