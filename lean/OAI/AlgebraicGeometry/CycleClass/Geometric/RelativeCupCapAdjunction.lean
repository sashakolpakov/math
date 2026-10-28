import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCup
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology
import OAI.AlgebraicTopology.Duality.Poincare.SupportRelativeCap
import OAI.AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient
import OAI.AlgebraicTopology.Products.CapCompatibility

/-! # Relative Cup Cap Adjunction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction

noncomputable section

/-!
# Evaluation adjunction for the genuine relative cup and cap products

The cap convention evaluates the front face first. Accordingly, the
sign-free adjunction has the relative cochain on the left of the cup:
evaluating `b cup a` on a relative chain equals evaluating `a` on `b cap z`.
The proof uses actual finite chains and the actual relative quotient.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CapCompatibility
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

/-- The actual rational cup evaluated on an integral finite chain is
adjoint to the actual mixed cap product, with no interchange of factors. -/
theorem rationalCup_evaluation_mixedCap (X : TopCat.{0}) (p q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q)
    (z : (LocalHomology.Cycles.integralSingularChains X).X (p + q)) :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) (p + q)
        (AlgebraicTopology.Products.Cup.singularCup X b a) z =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X q a
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSingularCap X p q b z) := by
  have h : AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) (p + q)
      (AlgebraicTopology.Products.Cup.singularCup X b a) =
      ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X q a).restrictScalars ℤ).comp
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSingularCap X p q b) := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalIntegralCoefficient
    intro s
    change AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) (p + q)
        (AlgebraicTopology.Products.Cup.singularCup X b a) (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) q a
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSimplicialCap (TopCat.toSSet.obj X) p q b
          (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s))
    rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex, AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.mixedSimplicialCap_simplex,
      map_smul, AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
    exact AlgebraicTopology.Products.Cup.evaluation_cup (TopCat.toSSet.obj X) b a s
  exact LinearMap.congr_fun h z

/-- Relative rational cup evaluation is adjoint to the genuine cap into
ordinary rational chains. Both sides factor through the actual quotient
by chains in the subspace. -/
theorem relativeAbsoluteCup_evaluation_cap (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (b : (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q)
    (z : (LocalHomology.Cycles.relativeSingularChains X A).X (p + q)) :
    AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X A (p + q)
        (RelativeCup.Cycles.relativeAbsoluteCup X A p q b a) z =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X q a
        (AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCap X A p q b z) := by
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeChainProjection_surjective X A (p + q) z
  rw [AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection, AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCap_projection,
    RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion]
  exact rationalCup_evaluation_mixedCap X p q
    ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p b) a z

/-- The same adjunction on the actual categorical cohomology and homology
groups. The relative factor is first in the cup, so no graded interchange
and no sign is used. -/
theorem relativeAbsoluteCohomologyCup_evaluation_cap
    (X : TopCat.{0}) (A : Set X) (p q : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (z : LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A (p + q)
        (RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCupWith X A (LinearMap.mul ℚ ℚ) p q b a) z =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X q a
        (AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology X A p q b z) := by
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p b
  obtain ⟨a, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) q a
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (LocalHomology.Cycles.relativeSingularChains X A) (p + q) z
  rw [RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCupWith_class_class, AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology_class_class,
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class]
  exact relativeAbsoluteCup_evaluation_cap X A p q b.val a.val z.val

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction
