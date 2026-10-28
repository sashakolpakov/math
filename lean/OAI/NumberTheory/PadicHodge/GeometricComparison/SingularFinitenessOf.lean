import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Singular Finiteness Of -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFinitenessOf.SingularFiniteness

noncomputable section

/-! Over a field, genuine singular homology and cohomology are finite dimensional together. -/

open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

variable (F : Type) [Field F] (X : TopCat.{0}) (n : ℕ)

theorem homology_of_cohomology [FiniteDimensional F (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of F F) X n)] :
    FiniteDimensional F ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n) := by
  let e := AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := F) X n
  let : FiniteDimensional F (Module.Dual F ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact (Module.finite_dual_iff F).mp inferInstance

theorem cohomology_of_homology [FiniteDimensional F ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n)] :
    FiniteDimensional F (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of F F) X n) :=
  Module.Finite.of_injective (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := F) X n).toLinearMap
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := F) X n).injective

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SingularFinitenessOf.SingularFiniteness
