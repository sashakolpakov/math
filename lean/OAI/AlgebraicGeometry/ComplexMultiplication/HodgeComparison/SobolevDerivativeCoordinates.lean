import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds

/-! # Sobolev Derivative Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDerivativeCoordinates.CM.Construction

noncomputable section

/-! Higher Sobolev regularity supplies genuine H1 coordinates for weak
derivatives, and spatial difference quotients converge in those coordinates. -/

open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem memSobolev_l2_iff_embedding_range {s : ℝ} (hs : 0 ≤ s)
    (u : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (u : 𝓢'(E, ℂ)) ↔
      ∃ v : Lp ℂ 2 (volume : Measure E), SobolevIs.CM.Construction.sobolevL2Embedding hs v = u := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := Bounds.CM.Construction.sobolevCoordinateMap_surjective E ℂ s ⟨u, hu⟩
    refine ⟨v, ?_⟩
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
    change (SobolevIs.CM.Construction.sobolevL2Embedding hs v : 𝓢'(E, ℂ)) = (u : 𝓢'(E, ℂ))
    rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution]
    exact congrArg Subtype.val hv
  · rintro ⟨v, rfl⟩
    rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨v, rfl⟩

theorem h2_coordinate_is_h1 (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev 2 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) :
    MemSobolev 1 2 (u : 𝓢'(E, ℂ)) := by
  rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff] at hu
  norm_num only [neg_add_cancel_left] at hu
  exact hu

/-- An H2 function has a derivative represented in the genuine H1 coordinates.
The spatial difference quotients converge in H1, not just in distributions. -/
theorem h2_difference_tendsto_h1_derivative (m : E) (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev 2 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) :
    ∃ v : Lp ℂ 2 (volume : Measure E),
      SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v = SobolevDifferential.CM.Construction.sobolevL2Derivative m u ∧
      Tendsto (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) (𝓝[≠] 0) (𝓝 v) := by
  obtain ⟨w, hw⟩ := (memSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp
    (h2_coordinate_is_h1 u hu)
  have hv := DifferenceConvergence.CM.Construction.l2DifferenceQuotient_tendsto_derivative m w
  rw [hw] at hv
  refine ⟨SobolevDifferential.CM.Construction.sobolevL2Derivative m w, ?_, hv⟩
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  have hJ := (J.continuous.tendsto (SobolevDifferential.CM.Construction.sobolevL2Derivative m w)).comp hv
  have hfun : (fun t : ℝ => J (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)) =
      (fun t : ℝ => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (J u)) := by
    funext t
    exact (DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolevEmbedding_comm m t (by norm_num : (0 : ℝ) ≤ 1) u).symm
  change Tendsto (fun t : ℝ => J (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u)) (𝓝[≠] 0)
    (𝓝 (J (SobolevDifferential.CM.Construction.sobolevL2Derivative m w))) at hJ
  rw [hfun] at hJ
  exact tendsto_nhds_unique hJ (DifferenceConvergence.CM.Construction.l2DifferenceQuotient_tendsto_derivative m u)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDerivativeCoordinates.CM.Construction
