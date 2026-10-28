import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CohomologyBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.TensorDualExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.EvaluationNaturality

/-! # Base Change Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.BaseChangeNaturality.ChainScalarExtension

noncomputable section

/-! The singular cohomology scalar comparison intertwines the actual pullbacks. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (R S : Type) [Field R] [Field S] [Algebra R S]
  {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
  [FiniteDimensional R ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)]
  [FiniteDimensional R ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y).homology n)]

theorem tensorCohomologyEquiv_tmul_naturality (a : S)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y n) :
    Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S X n
        (a ⊗ₜ[R] (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n) c) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of S S) f n)
        (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S Y n (a ⊗ₜ[R] c)) := by
  exact EvaluationNaturality.DualBaseChange.evaluation_comparison_naturality
    (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S X n) (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S Y n)
    (Intrinsic.HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n) (Intrinsic.HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S Y n)
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := R) X n) (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := R) Y n)
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) X n) (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := S) Y n)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n).hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of S S) f n).hom
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f n).hom (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := S) f n).hom
    (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv_evaluation R S X n) (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv_evaluation R S Y n)
    (fun c z => LinearMap.congr_fun (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularUniversalCoefficientEquiv_naturality (F := R) f n c) z)
    (fun c z => LinearMap.congr_fun (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularUniversalCoefficientEquiv_naturality (F := S) f n c) z)
    (fun z => Intrinsic.HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv_naturality R S f n (1 ⊗ₜ[R] z)) a c

theorem tensorCohomologyEquiv_naturality
    (x : S ⊗[R] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) Y n) :
    Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S X n
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n).hom.baseChange S x) =
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of S S) f n)
        (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S Y n x) := by
  let : Module R (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of S S) X n) :=
    Module.compHom _ (algebraMap R S)
  let : IsScalarTower R S (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of S S) X n) :=
    IsScalarTower.of_compHom R S _
  have h : (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S X n).toLinearMap.comp
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f n).hom.baseChange S) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of S S) f n).hom.comp
      (Intrinsic.CohomologyBaseChange.ChainScalarExtension.tensorCohomologyEquiv R S Y n).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    exact tensorCohomologyEquiv_tmul_naturality R S f n
  exact LinearMap.congr_fun h x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.BaseChangeNaturality.ChainScalarExtension
