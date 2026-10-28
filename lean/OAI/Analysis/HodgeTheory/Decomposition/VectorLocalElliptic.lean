import OAI.Analysis.HodgeTheory.Decomposition.VectorWeakCutoff
import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferenceBounds

/-! # Vector Local Elliptic -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic.Constructions

noncomputable section

/-! Interior second-derivative regularity for a genuine vector weak
equation with L² forcing and H¹ flux forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

theorem realL2Difference_eq_vector (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t u = VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u := by
  apply Lp.ext
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_coe m t u, VectorDifferences.Constructions.vectorL2DifferenceQuotient_coe m t u] with x hr hc
  rw [hr, hc, ← Complex.ofReal_inv]
  exact (IsScalarTower.algebraMap_smul ℂ t⁻¹ _).symm

variable [CompleteSpace F] [Fintype ι]

theorem vector_local_elliptic_flux_h2 (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    {L : NNReal} (hA : LipschitzWith L A) {C a c : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a) (hc : 0 ≤ c)
    (hgard : ∀ y : E, ∀ v : Lp F 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ ≤
        (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) +
          c * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp F 2 (volume : Measure E))
    (w : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : ∀ v : Lp F 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) +
        inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w)
          (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v))) :
    MemSobolev 2 2
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
        Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  have hAm := hA.continuous.aestronglyMeasurable (μ := (volume : Measure E))
  have hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  have heq := VectorWeakCutoff.Constructions.vector_weak_cutoff_flux b A hAm hCm g hg u f
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) w) hsol
  apply VectorElliptic.Constructions.vector_elliptic_flux_h2_regularity b A hA hC ha hc hgard _ _ _ heq
  intro i
  obtain ⟨B, hB⟩ := VectorCutoffDifferenceBounds.Constructions.vectorBoundedField_difference_bounded A hA hC _ (b i)
    (VectorCutoffDifferenceBounds.Constructions.vectorCutoffGradient_difference_bounded b g u (b i))
  refine ⟨(2 * Real.pi * ‖b i‖) * ‖VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g w‖ + B, fun t => ?_⟩
  rw [map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (hB t)
  rw [realL2Difference_eq_vector, ← VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding]
  exact VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolev_bound (b i) t _

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic.Constructions
