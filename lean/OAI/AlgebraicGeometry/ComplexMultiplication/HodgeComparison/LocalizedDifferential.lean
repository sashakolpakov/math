import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormChartLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents

/-! # Localized Differential -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedDifferential.CM.Construction

noncomputable section

/-! Localized weak differentiation of the actual global derivative graph. -/

open _root_.MeasureTheory Set Filter
open scoped SchwartzMap LineDeriv

def varietyDerivativeCutoffL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (m : EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) →L[ℝ] Lp ℂ 2 (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  ChartCutoffLp.CM.Construction.varietyChartCutoffL2 V e he (∂_{m} g) (ChartCutoffDerivative.CM.Construction.schwartz_derivative_compact_support g hgc m)
    ((SchwartzMap.tsupport_lineDerivOp_subset m g).trans hg)

theorem varietyLocalizedDifferential_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (i : ι) :
    SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) (ChartCutoffLp.CM.Construction.varietyScalarChartSobolevCoordinate V e he g hgc hg f) =
      varietyDerivativeCutoffL2 V e he g hgc hg (b i) (GlobalLp.CM.Construction.varietySmoothScalarL2 V f) +
      LpComponents.CM.Construction.complexLpComponent (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) i
        (OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b e he g hgc hg (GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f)) := by
  let G := ScalarChartLocalization.CM.Construction.varietyScalarChartCutoff V e he g hgc hg f
  let A := varietyDerivativeCutoffL2 V e he g hgc hg (b i) (GlobalLp.CM.Construction.varietySmoothScalarL2 V f)
  let W := OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b e he g hgc hg (GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b f)
  let B := LpComponents.CM.Construction.complexLpComponent (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) i W
  change SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 G) = A + B
  rw [SobolevDifferential.CM.Construction.sobolevL2Derivative_schwartz]
  apply Lp.ext
  have hA : A =ᵐ[volume] fun z => (∂_{b i} g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z •
      HolomorphicPrimitive.CM.Construction.zeroFormScalar f (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) :=
    ChartCutoffLp.CM.Construction.varietyChartCutoffL2_coe_of_ae V e he (∂_{b i} g) (ChartCutoffDerivative.CM.Construction.schwartz_derivative_compact_support g hgc (b i))
      ((SchwartzMap.tsupport_lineDerivOp_subset (b i) g).trans hg) _ _ (GlobalLp.CM.Construction.varietySmoothScalarL2_coe V f)
  have hW : W =ᵐ[volume] fun z => g z • GlobalLp.CM.Construction.varietyOneFormInChart V b e (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
      (e.symm (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) := OneFormChartLocalization.CM.Construction.varietyOneFormChartL2_form V C b e he g hgc hg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f)
  filter_upwards [(∂_{b i} G).coeFn_toLp 2 volume, Lp.coeFn_add A B, hA,
    LpComponents.CM.Construction.complexLpComponent_coe (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) i W, hW] with z hP hsum ha hb hw
  rw [hP, hsum]
  change (∂_{b i} G : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z = A z + B z
  rw [ha, hb, hw]
  by_cases hz : z ∈ tsupport g
  · exact ChartCutoffDerivative.CM.Construction.varietyScalarChartCutoff_derivative V e he b g hgc hg f (hg hz) i
  · have hGz : (∂_{b i} G : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (ChartCutoffDerivative.CM.Construction.varietyScalarChartCutoff_derivative_support V e he g hgc hg f (b i) h))
    have hdz : (∂_{b i} g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (SchwartzMap.tsupport_lineDerivOp_subset (b i) g h))
    rw [hGz, hdz, image_eq_zero_of_notMem_tsupport hz, zero_smul, zero_smul]
    simp

theorem varietyLocalizedDifferential (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (g : 𝓢(EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport (g : EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ))
    (hg : tsupport g ⊆ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b) (i : ι) :
    SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) (GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he g hgc hg u).val =
      varietyDerivativeCutoffL2 V e he g hgc hg (b i) (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b u) +
      LpComponents.CM.Construction.complexLpComponent (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) i
        (OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b e he g hgc hg (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b u)) := by
  let S := GlobalLocalization.CM.Construction.varietySobolevChartLocalization V C b e he g hgc hg
  let A := varietyDerivativeCutoffL2 V e he g hgc hg (b i)
  let L := OneFormChartLocalization.CM.Construction.varietyOneFormChartL2 V C b e he g hgc hg
  let P := LpComponents.CM.Construction.complexLpComponent (volume : Measure (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) i
  have hleft : Continuous (fun v : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b => SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) (S v).val) :=
    (SobolevDifferential.CM.Construction.sobolevL2Derivative (b i)).continuous.comp (continuous_subtype_val.comp S.continuous)
  have hright : Continuous (fun v : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b =>
      A (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b v) + P (L (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b v))) :=
    (A.continuous.comp (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).continuous).add
      (P.continuous.comp (L.continuous.comp (GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).continuous))
  have h := (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev_dense V C b).equalizer hleft hright (by
    funext f
    dsimp only [Function.comp_apply, S, A, L, P]
    rw [GlobalLocalization.CM.Construction.varietySobolevChartLocalization_smooth, GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth, GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth]
    exact varietyLocalizedDifferential_smooth V C b e he g hgc hg f i)
  exact congrFun h u

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalizedDifferential.CM.Construction
