import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RationalCompactFundamental
import OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison

/-! # Canonical Local Dual -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions

noncomputable section

/-! The canonical rational point class dual to the actual integral complex orientation. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.RationalCompactFundamental.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]

def canonicalLocalDual (x : M) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) ({x}ᶜ) (2 * d) :=
  (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M) ({x}ᶜ) (2 * d)).symm
    ((Int.castAddHom ℚ).toIntLinearMap.comp
      (Geometric.ComplexChartOrientation.Cycles.complexChartTopLocalIso (chartAt (Fin d → ℂ) x) x (mem_chart_source (Fin d → ℂ) x)).hom.hom)

theorem canonicalLocalDual_integralEvaluation (x : M) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x}ᶜ) (2 * d)
      (canonicalLocalDual d x) (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) = 1 := by
  change (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M) ({x}ᶜ) (2 * d))
    ((AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M) ({x}ᶜ) (2 * d)).symm _) _ = _
  rw [LinearEquiv.apply_symm_apply]
  change ((Geometric.ComplexChartOrientation.Cycles.complexChartTopLocalIso (chartAt (Fin d → ℂ) x) x
    (mem_chart_source (Fin d → ℂ) x)).toLinearEquiv
      (Geometric.ComplexChartOrientation.Cycles.complexChartLocalClass (chartAt (Fin d → ℂ) x) x (mem_chart_source (Fin d → ℂ) x)) : ℚ) = 1
  rw [Geometric.ComplexChartOrientation.Cycles.complexChartLocalClass_normalization, Int.cast_one]

theorem canonicalLocalDual_unique (x : M)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) ({x}ᶜ) (2 * d))
    (hc : AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x}ᶜ) (2 * d) c
      (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) = 1) : c = canonicalLocalDual d x := by
  apply (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M) ({x}ᶜ) (2 * d)).injective
  ext z
  obtain ⟨n, hn, _⟩ := Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass_generates (p := d) x z
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x}ᶜ) (2 * d) c z =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x}ᶜ) (2 * d) (canonicalLocalDual d x) z
  rw [← hn, map_zsmul, map_zsmul, hc, canonicalLocalDual_integralEvaluation]

theorem canonicalLocalDual_scalarEvaluation (x : M) :
    Geometric.RelativeChainD.Cycles.relativeHomologyEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of M) ({x}ᶜ) (2 * d)
      (canonicalLocalDual d x)
      (ProperImage.RationalCompactFundamental.Constructions.Construction.rationalizeRelativeClass (TopCat.of M) ({x}ᶜ) (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x)) = 1 :=
  (AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.relativeRationalHomologyEvaluation_eq_scalarEvaluation (TopCat.of M) ({x}ᶜ) (2 * d)
    (canonicalLocalDual d x) (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x)).symm.trans
    (canonicalLocalDual_integralEvaluation d x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions
