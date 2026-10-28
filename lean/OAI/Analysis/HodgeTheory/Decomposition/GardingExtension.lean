import OAI.Analysis.HodgeTheory.Decomposition.HodgeFrozenGradient
import OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension

/-! # Garding Extension -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GardingExtension.Constructions

noncomputable section

/-! Every actual projective chart point has a smooth bounded Lipschitz
extension of its Hodge principal coefficient satisfying genuine integrated
gradient coercivity, uniformly under spatial translation. -/

open _root_.MeasureTheory
open scoped ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

include he hz in
theorem projectiveHodge_exists_garding_extension :
    ∃ A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n,
      A =ᶠ[𝓝 z] GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n ∧
      ContDiff ℝ ∞ A ∧
      HasCompactSupport (fun x => A x - GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z) ∧
      (∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L A) ∧
      ∃ a : ℝ, 0 < a ∧
        ∀ (y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
          (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
            (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))),
          a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u‖ ^ 2 ≤
            ∫ x, inner ℝ
              (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u x))
              (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) u x) := by
  obtain ⟨a₀, ha₀, h₀⟩ := HodgeFrozenGradient.Constructions.projectiveFrozenGradient_coercive V e n he z hz
  obtain ⟨A, hlocal, hsmooth, hcompact, hclose, hbound, hLip⟩ :=
    SmoothFrozenExtension.Constructions.exists_smooth_frozen_extension (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n)
      (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient_smooth V e n he) hz (half_pos ha₀)
  refine ⟨A, hlocal, hsmooth, hcompact, hbound, hLip, a₀ / 2, half_pos ha₀, fun y u => ?_⟩
  obtain ⟨C, hC⟩ := hbound
  have hε : ∀ x, ‖GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z - A x‖ ≤ a₀ / 2 := by
    intro x
    rw [norm_sub_rev]
    exact hclose x
  have h := GradientGarding.Constructions.gradient_garding_small_perturbation
    (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z)
    A hsmooth.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) hε h₀ y u
  convert h using 1
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.GardingExtension.Constructions
