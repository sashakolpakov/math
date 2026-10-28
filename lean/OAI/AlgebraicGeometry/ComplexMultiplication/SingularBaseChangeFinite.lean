import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarExtensionObject
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Singular Base Change Finite -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChangeFinite

noncomputable section

/-! # Finiteness under the actual singular coefficient base change -/

open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Finite rational singular homology gives finite complex singular homology. -/
theorem rationalComplexSingularHomology_finite (Y : TopCat.{0}) (n : ℕ)
    [FiniteDimensional ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)] :
    FiniteDimensional ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y n) := by
  let e := (SingularBaseChange.rationalComplexSingularHomologyIso Y n).toLinearEquiv
  have : FiniteDimensional ℂ (SingularBaseChange.rationalComplexScalars.obj (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)) := by
    let t := ScalarExtensionObject.rationalComplexScalarsTensorEquiv (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)
    exact FiniteDimensional.of_injective t.toLinearMap t.injective
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

set_option backward.isDefEq.respectTransparency false in
/-- Base change preserves the dimension of the actual singular homology. -/
theorem rationalComplexSingularHomology_finrank (Y : TopCat.{0}) (n : ℕ) :
    Module.finrank ℂ (AlgebraicTopology.Singular.Cohomology.Homology ℂ Y n) =
      Module.finrank ℚ (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n) := by
  let e := (SingularBaseChange.rationalComplexSingularHomologyIso Y n).toLinearEquiv
  calc
    _ = Module.finrank ℂ (SingularBaseChange.rationalComplexScalars.obj (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)) :=
      e.symm.finrank_eq
    _ = Module.finrank ℂ (ℂ ⊗[ℚ] (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)) :=
      (ScalarExtensionObject.rationalComplexScalarsTensorEquiv (AlgebraicTopology.Singular.Cohomology.Homology ℚ Y n)).finrank_eq
    _ = _ := Module.finrank_baseChange

/-- Both genuine singular coefficient theories have finite-dimensional degree-one
cohomology in the original CM setting. -/
theorem cmH1Data_complexSingularCohomology_finite
    (X : Over (AlgebraicGeometry.Spec ↧ℂ))
    [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.Smooth X.hom]
    [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (d : Definitions.CMH1Data X) :
    FiniteDimensional ℂ (AlgebraicTopology.Singular.CohomologyTo.Cohomology ℂ ↧(ComplexPoint.Basic.ComplexSchemePoint X) 1) := by
  let Y : TopCat.{0} := ↧(ComplexPoint.Basic.ComplexSchemePoint X)
  let := Coefficient.Finite.cmH1Data_singularHomology_finite X d
  let := rationalComplexSingularHomology_finite Y 1
  let e := AlgebraicTopology.Singular.CohomologyTo.cohomologyEquivDualHomology ℂ Y 1
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

end

end OAI.AlgebraicGeometry.ComplexMultiplication.SingularBaseChangeFinite
