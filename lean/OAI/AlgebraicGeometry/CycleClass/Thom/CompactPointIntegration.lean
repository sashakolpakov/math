import OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees

/-! # Compact Point Integration -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions

noncomputable section

/-! A canonical fiber point contributes exactly one under slant with the compact fundamental class. -/

open _root_.CategoryTheory
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.Slant.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.ExteriorCrossDegrees.Constructions.Slant

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

omit [T2Space M] in
theorem pointComplementMapsTo (K : Set M) (x : M) (hx : x ∈ K) :
    Set.MapsTo (𝟙 (TopCat.of M)) Kᶜ ({x}ᶜ) := by
  intro y hy hyx
  change y = x at hyx
  exact hy (hyx.symm ▸ hx)

def compactPointClass (K : Set M) (x : M) (hx : x ∈ K) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) Kᶜ (2 * d) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of M))
    (pointComplementMapsTo K x hx) (2 * d) (CanonicalLocalDual.Constructions.canonicalLocalDual d x)

theorem compactPointClass_evaluation (K : Set M) (hK : IsCompact K) (x : M) (hx : x ∈ K) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of M) Kᶜ (2 * d)
      (compactPointClass d K x hx) (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK) = 1 := by
  have he := AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.relativeRationalHomologyEvaluation_eq_scalarEvaluation (TopCat.of M) Kᶜ (2 * d)
    (compactPointClass d K x hx) (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK)
  refine he.symm.trans ?_
  rw [compactPointClass, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x}ᶜ) (2 * d)
    (CanonicalLocalDual.Constructions.canonicalLocalDual d x)
    (Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * d)
      (Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK)) = 1
  rw [Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint, CanonicalLocalDual.Constructions.canonicalLocalDual_integralEvaluation]

theorem slant_compactPoint (X : TopCat.{0}) (A : Set X) (hA : IsOpen A) (p : ℕ)
    (K : Set M) (hK : IsCompact K) (x : M) (hx : x ∈ K)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p) :
    Relative.Slant.Constructions.slant ℚ X (TopCat.of M) A Kᶜ p (2 * d) (p + 2 * d) rfl
      (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalCompactFundamentalClass d K hK)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X (TopCat.of M) A Kᶜ hA hK.isClosed.isOpen_compl p (2 * d)
        a (compactPointClass d K x hx)) = a := by
  rw [Relative.ExteriorCrossDegrees.Constructions.Slant.slant_exterior, compactPointClass_evaluation, one_smul]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions
