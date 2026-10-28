import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD
import OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCapTrace

/-! # Ordinary Relative Cap Adjunction -/

namespace OAI.AlgebraicTopology.Products.OrdinaryRelativeCapAdjunction

noncomputable section

/-!
# Evaluation adjunction for ordinary cap acting on relative homology

The actual ordinary/relative cap product is adjoint to the actual
ordinary/relative cup product. The proof lifts a relative chain to an
ambient chain without imposing an absolute cycle condition on that lift.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.LocallyFiniteCapTrace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine right small-quotient cap representative satisfies cup/cap
evaluation on every relative integral chain, before taking homology. -/
theorem ordinaryRelativeSmallCap_evaluation
    (X : TopCat.{0}) (B : Set X) (p q : ℕ)
    (a : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B).X q)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B).X (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X B q b
        (Duality.Poincare.TwoSupportRelativeCap.twoSupportSmallCap X ∅ B p q
          ((Duality.Poincare.CapRelativeTrace.relativeEmptyCochainsIso (ModuleCat.of ℚ ℚ) X).inv.f p a)
          ((AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementRight X ∅ B).f (p + q) z)) =
      Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv X B (p + q)
        (AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup X B p q a b) z := by
  obtain ⟨z, rfl⟩ := Duality.Poincare.SupportRelativeCap.relativeChainProjection_surjective X B (p + q) z
  rw [Duality.Poincare.LocallyFiniteCapTrace.twoSupportSmallCap_empty_projection,
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeDegreewiseChainDualEquiv_projection,
    Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv_projection,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_inclusion]
  exact (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCapAdjunction.Cycles.rationalCup_evaluation_mixedCap X p q a
    ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X B).f q b) z).symm

/-- The scalar relative-homology evaluation of the actual cap output is
the mixed integral-homology evaluation of the actual relative cup product.
The factor order is unchanged, so this identity has no graded sign. -/
theorem ordinaryRelativeCapHomology_evaluation
    (X : TopCat.{0}) (B : Set X) (hB : IsOpen B) (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B q)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X B (p + q)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) X B q b
        (Duality.Poincare.CapRelativeTrace.ordinaryRelativeCapHomology X B hB p q a z) =
      Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X B (p + q)
        (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup X B p q a b) z := by
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X p a
  obtain ⟨b, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X B) q b
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X B) (p + q) z
  rw [Duality.Poincare.LocallyFiniteCapTrace.ordinaryRelativeCapHomology_class_class,
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation_class_class,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup_class_class,
    Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class]
  exact ordinaryRelativeSmallCap_evaluation X B p q a.val b.val z.val

end

end OAI.AlgebraicTopology.Products.OrdinaryRelativeCapAdjunction
