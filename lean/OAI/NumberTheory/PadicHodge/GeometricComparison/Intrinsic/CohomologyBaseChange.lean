import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HomologyBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.DualBase
import OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFinitenessOf

/-! # Cohomology Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CohomologyBaseChange.ChainScalarExtension

noncomputable section

/-! Scalar extension of actual singular cohomology through canonical evaluation and homology base change. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (R S : Type) [Field R] [Field S] [Algebra R S]
  (X : TopCat.{0}) (n : ℕ)
  [FiniteDimensional R ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)]

def tensorCohomologyEquiv :
    (S ⊗[R] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) ≃ₗ[S]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of S S) X n :=
  ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := R) X n).baseChange R S _ _).trans
    ((DualBase.DualBaseChange.equiv S ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)).trans
      ((Module.Dual.congr (HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n)).trans
        (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) X n).symm))

theorem tensorCohomologyEquiv_evaluation (a : S)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) :
    AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) X n
        (tensorCohomologyEquiv R S X n (a ⊗ₜ[R] c))
        (HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n (1 ⊗ₜ[R] z)) =
      a * algebraMap R S (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := R) X n c z) := by
  change (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) X n)
      ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) X n).symm _) _ = _
  rw [LinearEquiv.apply_symm_apply]
  change DualBase.DualBaseChange.equiv S ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)
    (a ⊗ₜ[R] AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := R) X n c)
    ((HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n).symm ((HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n) (1 ⊗ₜ[R] z))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact DualBase.DualBaseChange.equiv_tmul_one a _ z

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CohomologyBaseChange.ChainScalarExtension
