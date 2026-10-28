import OAI.Analysis.HodgeTheory.Decomposition.WeakAllOrders
import OAI.Analysis.HodgeTheory.Decomposition.CutoffExistence
import OAI.Analysis.HodgeTheory.Decomposition.RegularityCutoffs
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Weak Smooth Neighborhood -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothNeighborhood.Constructions

noncomputable section

/-! Actual manifold weak Hodge solutions with genuine smooth forcing
have smooth local representatives around every chart point. -/

open _root_.MeasureTheory Set TemperedDistribution
open scoped SchwartzMap ContDiff _root_.Manifold _root_.Topology
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he in
theorem exists_projective_weak_smooth_neighborhood
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n)
    (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f))
    (x : V.analyticSpace) (hx : x ∈ e.source) :
    ∃ χ : V.analyticSpace → ℝ,
      ∃ hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ,
      ∃ hχs : tsupport χ ⊆ e.source,
        χ =ᶠ[𝓝 x] 1 ∧
        ∃ g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g ∧
          tsupport g ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧ (∀ z, g z = Complex.ofReal (g z).re) ∧
          g =ᶠ[𝓝 (MeasureVolume.Constructions.chartCoordinateForward V e x)] 1 ∧
          ∃ v : BoundedContinuousFunction (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
              (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
            AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution v =
              (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g
                (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) χ hχ hχs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) :
                𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) ∧
            ContDiff ℝ (⊤ : ℕ∞) (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → _) := by
  obtain ⟨χ, hχ, hχs, hχnear, hbound⟩ := CutoffExistence.Constructions.exists_projective_h1_cutoff V e he n x hx
  obtain ⟨W, hWχ, hW, hxW⟩ := mem_nhds_iff.mp hχnear
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx
  have hzW : MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ W := by
    rw [MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx]
    exact hxW
  obtain ⟨A, hAlocal, hAsmooth, hAc, ⟨C, hC⟩, ⟨L, hA⟩, a, ha, hgard⟩ :=
    GardingExtension.Constructions.projectiveHodge_exists_garding_extension V e n he z hz
  obtain ⟨T, hTopen, hzT, hTchart, hTW, hAT, τ, hτc, hτs, hτreal, hτT, g, hgc, hgT, hgreal, hgnear⟩ :=
    RegularityCutoffs.Constructions.exists_projective_regularity_cutoffs V e n z hz hW hzW A hAlocal
  let η := fun z => (τ z).re
  have hη : ContDiff ℝ ∞ η := Complex.reCLM.contDiff.comp (τ.smooth ⊤)
  have hηc : HasCompactSupport η := RegularityCutoffs.Constructions.schwartz_realPart_compact τ hτc
  have hηs : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := (RegularityCutoffs.Constructions.schwartz_realPart_tsupport τ).trans hτs
  have hηT : ∀ z ∈ T, η z = 1 := by
    intro z hz
    change (τ z).re = 1
    rw [hτT z hz, Complex.one_re]
  have horders := WeakAllOrders.Constructions.projectiveWeakHodgeSolution_local_all_orders V e he n χ hχ hχs hbound η hη hηc hηs
    τ hτc hτs hτreal A (GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n z) hAsmooth hAc hA hC ha hgard
    T hTopen hTchart hW hTW (fun y hy => hWχ hy) hηT hAT hτT u f hsol g hgc hgreal hgT
  have hlocal : ∀ s : ℕ, MemSobolev (s : ℝ) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g
        (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he (n + 1) χ hχ hχs (EnergyDomain.Constructions.projectiveEnergyInclusion V n u)) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
    intro s
    have hs := horders s
    rw [VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding,
      VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization_L2 V e he n χ hχ hχs hbound] at hs
    exact hs
  obtain ⟨v, hv, hvsmooth⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction.sobolev_all_orders_smooth hlocal
  exact ⟨χ, hχ, hχs, hχnear, g, hgc, hgT.trans hTchart, hgreal, hgnear, v, hv, hvsmooth⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakSmoothNeighborhood.Constructions
