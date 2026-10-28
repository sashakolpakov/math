import OAI.AlgebraicTopology.Kunneth.CapFinitenessOf
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Projective Finiteness Le -/

namespace OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

noncomputable section

/-! Finiteness of rational cohomology, obtained from the actual cap duality. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient OAI.AlgebraicTopology.Duality.Poincare.Manifold
open scoped _root_.Manifold

namespace Construction.ProjectiveFiniteness

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem manifold_homology_finite_of_le (q : ℕ) (hq : q ≤ 2 * d) :
    FiniteDimensional ℚ ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q) := by
  let p := 2 * d - q
  have hpq : p + q = 2 * d := Nat.sub_add_cancel hq
  let z := Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of M) (p + q)
    (Duality.Poincare.CompactMeaning.complexFundamentalClassInDegree d (M := M) (p + q) hpq)
  apply CapFinitenessOf.Construction.CapFiniteness.finite_homology_of_cap_surjective (TopCat.toSSet.obj (TopCat.of M)) p q z
  exact (Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality d (M := M) p q hpq).toLinearEquiv.surjective

include d in
/-- Compact complex manifolds have finite-dimensional rational cohomology
 in every degree, including degrees above their real dimension. -/
theorem manifold_cohomology_finite (p : ℕ) :
    FiniteDimensional ℚ (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) := by
  by_cases hp : p ≤ 2 * d
  · let q := 2 * d - p
    have hpq : p + q = 2 * d := Nat.add_sub_of_le hp
    let : FiniteDimensional ℚ
        ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q) :=
      manifold_homology_finite_of_le d q (Nat.sub_le _ _)
    exact Module.Finite.of_injective
      (Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality d (M := M) p q hpq).toLinearEquiv.toLinearMap
      (Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality d (M := M) p q hpq).toLinearEquiv.injective
  · let : Subsingleton (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
      ModuleCat.subsingleton_of_isZero
        (Duality.Poincare.Manifold.compactComplexManifold_singularCohomology_isZero d (M := M) p (by omega))
    infer_instance

/-- The manifold hypotheses hold for the actual analytic realization. -/
theorem integralProjective_cohomology_finite (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    FiniteDimensional ℚ (V.rationalCohomology n) :=
  manifold_cohomology_finite V.complexDimension (M := V.analyticSpace) n

/-- The finite clopen component decomposition covers arbitrary smooth
 projective presentations, including the empty variety. -/
theorem projective_cohomology_finite (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    FiniteDimensional ℚ (P.rationalCohomology n) := by
  let : ∀ C : irreducibleComponents P.carrier,
      FiniteDimensional ℚ ((P.componentVariety C).rationalCohomology n) :=
    fun C => integralProjective_cohomology_finite (P.componentVariety C) n
  exact Module.Finite.of_injective
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) n).toLinearMap
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) n).injective

theorem finite_homology_of_finite_cohomology {k : Type} [Field k]
    (X : TopCat.{0}) (n : ℕ)
    [FiniteDimensional k (Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X n)] :
    FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n) := by
  let : Module.Finite k (Module.Dual k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n)) :=
    Module.Finite.of_surjective (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).toLinearMap
      (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).surjective
  exact (Module.finite_dual_iff k).mp inferInstance

theorem projective_homology_finite (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    FiniteDimensional ℚ
      ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace P.toOver)).homology n) := by
  let : FiniteDimensional ℚ (P.rationalCohomology n) := projective_cohomology_finite P n
  exact finite_homology_of_finite_cohomology (AlgebraicGeometry.Betti.Scheme.schemePointSpace P.toOver) n

end Construction.ProjectiveFiniteness

end

end OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
