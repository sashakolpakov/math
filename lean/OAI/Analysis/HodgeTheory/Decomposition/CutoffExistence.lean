import OAI.Analysis.HodgeTheory.Decomposition.VectorEnergyLocalization
import Mathlib.Geometry.Manifold.BumpFunction

/-! # Cutoff Existence -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CutoffExistence.Constructions

noncomputable section

/-! Around every actual manifold chart point there is a real cutoff
equal to one nearby whose H¹ coefficient localization is graph-bounded. -/

open Set _root_.Metric
open scoped _root_.Manifold ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he in
theorem exists_projective_h1_cutoff (x : V.analyticSpace) (hx : x ∈ e.source) :
    ∃ χ : V.analyticSpace → ℝ,
      ∃ hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ,
      ∃ hχs : tsupport χ ⊆ e.source,
        χ =ᶠ[𝓝 x] 1 ∧
        ∃ B : ℝ, ∀ a, ‖VectorEnergyLocalization.Constructions.projectiveVectorH1Localization V e he (n + 1) χ hχ hχs a‖ ≤
          B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖ := by
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx
  obtain ⟨r, hr, _, hbound⟩ := VectorEnergyLocalization.Constructions.projectiveVectorH1Localization_local_bound V e he n z hz
  let U := e.source ∩ MeasureVolume.Constructions.chartCoordinateForward V e ⁻¹' ball z r
  have hU : IsOpen U := ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm.continuous.comp_continuousOn
    e.continuousOn).isOpen_inter_preimage e.open_source isOpen_ball
  have hxU : x ∈ U := ⟨hx, mem_ball_self hr⟩
  obtain ⟨χ, _, hs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, V.analyticModel)) x).mem_iff.mp
    (hU.mem_nhds hxU)
  have hχs : tsupport χ ⊆ e.source := hs.trans inter_subset_left
  have hball : MeasureVolume.Constructions.chartCoordinateForward V e '' tsupport χ ⊆ closedBall z r := by
    rintro _ ⟨y, hy, rfl⟩
    exact ball_subset_closedBall (hs hy).2
  obtain ⟨B, _, hB⟩ := hbound χ χ.contMDiff hχs hball
  exact ⟨χ, χ.contMDiff, hχs, χ.eventuallyEq_one, B, hB⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.CutoffExistence.Constructions
