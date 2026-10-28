import OAI.Analysis.HodgeTheory.Decomposition.Weak
import OAI.Analysis.HodgeTheory.Decomposition.CutoffExistence
import OAI.Analysis.HodgeTheory.Decomposition.RegularityCutoffs

/-! # Weak Neighborhood -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakNeighborhood.Constructions

noncomputable section

/-! Unconditional interior H² regularity of actual completed manifold
weak Hodge solutions with arbitrary genuine L² forcing. -/

open _root_.MeasureTheory Set TemperedDistribution
open scoped SchwartzMap ContDiff _root_.Manifold _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he in
theorem exists_projective_weak_h2_neighborhood
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) (f : Form.Constructions.ProjectiveL2Forms V (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u f)
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    ∃ χ : V.analyticSpace → ℝ,
      ∃ hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ,
      ∃ hχs : tsupport χ ⊆ e.source,
        χ =ᶠ[𝓝 x] 1 ∧
        ∃ T : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), IsOpen T ∧ MeasureVolume.Constructions.chartCoordinateForward V e x ∈ T ∧
          T ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
          ∀ (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)), HasCompactSupport g →
            (∀ z, g z = Complex.ofReal (g z).re) → tsupport g ⊆ T →
            MemSobolev 2 2
              (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g
                (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) χ hχ hχs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) :
                𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  obtain ⟨χ, hχ, hχs, hχnear, hbound⟩ := CutoffExistence.Constructions.exists_projective_h1_cutoff V e he n x hx
  obtain ⟨W, hWχ, hW, hxW⟩ := mem_nhds_iff.mp hχnear
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx
  have hzW : MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ W := by
    rw [MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx]
    exact hxW
  obtain ⟨A, hAlocal, _hAsmooth, _hAc, ⟨C, hC⟩, ⟨L, hA⟩, a, ha, hgard⟩ :=
    GardingExtension.Constructions.projectiveHodge_exists_garding_extension V e n he z hz
  obtain ⟨T, hTopen, hzT, hTchart, hTW, hAT, τ, hτc, hτs, _hτreal, hτT, _⟩ :=
    RegularityCutoffs.Constructions.exists_projective_regularity_cutoffs V e n z hz hW hzW A hAlocal
  let η := fun z => (τ z).re
  have hη : ContDiff ℝ ∞ η := Complex.reCLM.contDiff.comp (τ.smooth ⊤)
  have hηc : HasCompactSupport η := RegularityCutoffs.Constructions.schwartz_realPart_compact τ hτc
  have hηs : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := (RegularityCutoffs.Constructions.schwartz_realPart_tsupport τ).trans hτs
  have hηT : ∀ z ∈ T, η z = 1 := by
    intro z hz
    change (τ z).re = 1
    rw [hτT z hz, Complex.one_re]
  refine ⟨χ, hχ, hχs, hχnear, T, hTopen, hzT, hTchart, fun g hgc hgreal hgT => ?_⟩
  have hH2 := Weak.Constructions.projectiveWeakHodgeSolution_local_h2 V e he n χ hχ hχs hbound η hη hηc hηs
    τ hτc hτs A hA hC ha hgard T hTchart hW hTW (fun y hy => hWχ hy) hηT hAT hτT
    u f hsol g hgc hgreal hgT
  rw [VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding, VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization_L2 V e he n χ hχ hχs hbound] at hH2
  exact hH2

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakNeighborhood.Constructions
