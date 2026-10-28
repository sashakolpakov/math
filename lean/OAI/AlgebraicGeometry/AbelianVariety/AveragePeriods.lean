import OAI.AlgebraicGeometry.AbelianVariety.LogDerivative
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration
import Mathlib.MeasureTheory.Integral.Prod

/-! # Average Periods -/

namespace OAI.AlgebraicGeometry.AbelianVariety.AveragePeriods.Constructions.ExteriorCohomology

noncomputable section

/-!
# Averaging actual period integrals for ExteriorCohomology

Translated pullback integrands are jointly continuous and integrable on the
compact group times the unit cube. Fubini therefore proves that Haar averaging
commutes with actual cube and smooth-simplex integration.
-/

open scoped _root_.Manifold ContDiff _root_.Topology Simplicial
open Set Filter _root_.MeasureTheory
open OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration

variable {E G V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [Measure.IsMulRightInvariant μ]

theorem pullback_averageForms_toNormedSpace (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ σ) (t : V) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback σ hσ (Averaging.Constructions.ExteriorCohomology.averageForms μ form)).toNormedSpace t =
      ∫ g, LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ g t ∂μ := by
  let T : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) σ t
  let L : (E [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] (V [⋀^Fin n]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM T
  change L ((Averaging.Constructions.ExteriorCohomology.averageForms μ form) (σ t)) = ∫ g, L (AveragingDerivative.Constructions.ExteriorCohomology.translatedValue form g (σ t)) ∂μ
  rw [AveragingDerivative.Constructions.ExteriorCohomology.averageForms_eq_integral_pullback]
  exact (L.integral_comp_comm ((AveragingDerivative.Constructions.ExteriorCohomology.translatedValue_continuous form (σ t)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))).symm

theorem pullback_averageForms_apply (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : V → G) (hσ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ σ) (t : V) (v : Fin n → V) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback σ hσ (Averaging.Constructions.ExteriorCohomology.averageForms μ form)).toNormedSpace t v =
      ∫ g, LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ g t v ∂μ := by
  rw [pullback_averageForms_toNormedSpace]
  let L : (V [⋀^Fin n]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V) ℂ v).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hc : Continuous (fun g => LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ g t) :=
    (LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue_continuous form σ hσ).comp (continuous_id.prodMk continuous_const)
  exact (L.integral_comp_comm (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))).symm

omit [Measure.IsMulRightInvariant μ] in
theorem translatedCubeIntegrand_integrable (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube E G n) :
    Integrable (fun p : G × (Fin n → ℝ) =>
      LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ.toFun p.1 p.2 (fun j => Pi.single j 1))
      (μ.prod (volume.restrict (Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1)))) := by
  let cube : Set (Fin n → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  let F : G × (Fin n → ℝ) → ℂ := fun p =>
    LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ.toFun p.1 p.2 (fun j => Pi.single j 1)
  have hF : Continuous F :=
    (LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue_continuous form σ.toFun σ.smooth).eval continuous_const
  have h : IntegrableOn F (univ ×ˢ cube) (μ.prod volume) :=
    hF.continuousOn.integrableOn_compact' (isCompact_univ.prod isCompact_Icc)
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Icc)
  change Integrable F ((μ.prod volume).restrict (univ ×ˢ cube)) at h
  rw [← Measure.prod_restrict, Measure.restrict_univ] at h
  exact h

omit [Measure.IsMulRightInvariant μ] in
theorem manifoldCubeIntegration_translated_integrable (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube E G n) :
    Integrable (fun g => AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration σ
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form)) μ := by
  have hi := (translatedCubeIntegrand_integrable μ form σ).integral_prod_left
  apply hi.congr
  apply ae_of_all
  intro g
  exact (AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral σ
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form)).symm

theorem manifoldCubeIntegration_averageForms (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.SmoothManifoldCube E G n) :
    AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration σ (Averaging.Constructions.ExteriorCohomology.averageForms μ form) =
      ∫ g, AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration σ
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
          (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) ∂μ := by
  let F : G × (Fin n → ℝ) → ℂ := fun p =>
    LogDerivative.Constructions.ExteriorCohomology.translatedPullbackValue form σ.toFun p.1 p.2 (fun j => Pi.single j 1)
  have hFI := translatedCubeIntegrand_integrable μ form σ
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral]
  have he : ∀ t, AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubePullback σ (Averaging.Constructions.ExteriorCohomology.averageForms μ form) t (fun j => Pi.single j 1) =
      ∫ g, F (g, t) ∂μ := fun t => pullback_averageForms_apply μ form σ.toFun σ.smooth t _
  simp_rw [he]
  rw [← integral_integral_swap hFI]
  apply integral_congr_ae
  apply ae_of_all
  intro g
  exact (AlgebraicTopology.DeRham.Comparison.ManifoldCubeIntegration.manifoldCubeIntegration_eq_integral σ
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form)).symm

theorem smoothSimplexIntegration_averageForms (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet _⦋n⦌) :
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ (Averaging.Constructions.ExteriorCohomology.averageForms μ form) =
      ∫ g, AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
          (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) ∂μ := by
  simp only [AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_apply]
  rw [manifoldCubeIntegration_averageForms, integral_smul]

omit [Measure.IsMulRightInvariant μ] in
theorem smoothSimplexIntegration_translated_integrable (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet _⦋n⦌) :
    Integrable (fun g => AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form)) μ :=
  (manifoldCubeIntegration_translated_integrable μ form (AlgebraicTopology.DeRham.Comparison.ManifoldSimplexCube.manifoldSimplexCube σ)).smul ((-1 : ℝ) ^ n)

end

end OAI.AlgebraicGeometry.AbelianVariety.AveragePeriods.Constructions.ExteriorCohomology
