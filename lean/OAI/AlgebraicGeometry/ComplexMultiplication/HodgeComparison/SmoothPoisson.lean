import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DerivativeKernel
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalWeakSolver

/-! # Smooth Poisson -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPoisson.CM.Construction

noncomputable section

/-! Smooth Poisson solvability for the genuine global projective metric.
The compatibility condition is orthogonality to locally constant functions. -/

open _root_.MeasureTheory

theorem variety_smooth_poisson_exists (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hF : ∀ c : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      IsLocallyConstant (HolomorphicPrimitive.CM.Construction.zeroFormScalar c) →
        inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalLp.CM.Construction.varietySmoothScalarL2 V c) = 0) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      ∀ v : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
        (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x
          (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x))
          (GlobalLp.CM.Construction.varietyOneFormField V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v) x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
          inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalLp.CM.Construction.varietySmoothScalarL2 V v) := by
  let ℓ : GlobalSobolevGraph.CM.Construction.varietySobolevGraph V C b →L[ℝ] ℝ :=
    (innerSL ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F)).comp ((GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b).restrictScalars ℝ)
  have hℓ : ∀ u ∈ ((GlobalSobolevGraph.CM.Construction.varietySobolevDerivative V C b).restrictScalars ℝ).ker, ℓ u = 0 := by
    intro u hu
    obtain ⟨c, rfl, hc⟩ := (DerivativeKernel.CM.Construction.derivative_eq_zero_iff_locallyConstant V C b u).mp hu
    change inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b c)) = 0
    rw [GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth]
    exact hF c hc
  obtain ⟨u, hu, _⟩ := GlobalWeakSolver.CM.Construction.variety_metric_weak_existsUnique V C b ℓ hℓ
  have hsol : GlobalInteriorSmooth.CM.Construction.IsGlobalWeakMetricSolution V C b u.val F := hu
  obtain ⟨f, hf⟩ := GlobalSmoothSolution.CM.Construction.globalWeakMetricSolution_smooth V C b u.val F hsol
  refine ⟨f, fun v => ?_⟩
  have h := hu (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b v)
  rw [← hf, GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth, GlobalSobolevGraph.CM.Construction.varietySobolevDerivative_smooth] at h
  change (∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x
    (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x))
    (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v) x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) =
      inner ℝ (GlobalLp.CM.Construction.varietySmoothScalarL2 V F) (GlobalSobolevGraph.CM.Construction.varietySobolevFunction V C b (GlobalSobolevGraph.CM.Construction.varietySmoothToSobolev V C b v)) at h
  rw [GlobalSobolevGraph.CM.Construction.varietySobolevFunction_smooth] at h
  calc
    _ = ∫ x, inner ℝ (GlobalMetricCoefficient.CM.Construction.varietyGlobalMetricCoefficient V C b x
        (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) x))
        (GlobalLp.CM.Construction.varietyOneFormL2 V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v) x) ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V := by
      apply integral_congr_ae
      filter_upwards [GlobalLp.CM.Construction.varietyOneFormL2_coe V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f),
        GlobalLp.CM.Construction.varietyOneFormL2_coe V C b (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d v)] with x hx hy
      rw [hx, hy]
    _ = _ := h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPoisson.CM.Construction
