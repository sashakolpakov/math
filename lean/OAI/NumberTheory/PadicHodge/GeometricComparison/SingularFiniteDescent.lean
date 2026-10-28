import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HomologyBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFinitenessOf
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.FiniteScalarExtension

/-! # Singular Finite Descent -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFiniteDescent.SingularFiniteness

noncomputable section

/-! Finite-dimensional singular cohomology descends along an extension of coefficient fields. -/

variable (R S : Type) [Field R] [Field S] [Algebra R S] (X : TopCat.{0}) (n : ℕ)

theorem cohomology_descends [FiniteDimensional S (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of S S) X n)] :
    FiniteDimensional R (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X n) := by
  let : FiniteDimensional S ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := S) X).homology n) :=
    SingularFinitenessOf.SingularFiniteness.homology_of_cohomology S X n
  let : FiniteDimensional R ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) :=
    Finite.FiniteScalarExtension.ScalarExtension.finite_of_comparison R S _ (Intrinsic.HomologyBaseChange.ChainScalarExtension.tensorHomologyEquiv R S X n)
  exact SingularFinitenessOf.SingularFiniteness.cohomology_of_homology R X n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFiniteDescent.SingularFiniteness
