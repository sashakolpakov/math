import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralEvaluation
import OAI.AlgebraicTopology.FundamentalClass.FormPartition

/-! # Unsigned Chart Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnsignedChartIntegral.CM

noncomputable section

/-! ThetaCycle: the ordinary coefficient integral in a fixed real chart,
including genuine smooth cutoffs and finite linear decompositions. -/

open Set _root_.MeasureTheory
open OAI.AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction
open scoped _root_.Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def unsignedChartIntegrand (e : OpenPartialHomeomorph M (Fin d → ℝ)) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] ((Fin d → ℝ) → ℂ) where
  toFun form := e.target.indicator (fun y => form.val.inChart e y (Pi.basisFun ℝ (Fin d)))
  map_add' form other := by
    ext y
    by_cases hy : y ∈ e.target <;> simp [hy, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart]
  map_smul' c form := by
    ext y
    by_cases hy : y ∈ e.target <;> simp [hy, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart]

theorem unsigned_chart_integrand_weight (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ ρ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    unsignedChartIntegrand e (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm ρ hρ form) =
      Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff e ρ (fun y => form.val.inChart e y (Pi.basisFun ℝ (Fin d))) := by
  ext y
  by_cases hy : y ∈ e.target
  · simp only [unsignedChartIntegrand, LinearMap.coe_mk, AddHom.coe_mk, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff,
      indicator_of_mem hy, AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm_inChart, Complex.real_smul]
  · simp only [unsignedChartIntegrand, LinearMap.coe_mk, AddHom.coe_mk, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff,
      indicator_of_notMem hy]

omit [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] in
theorem unsigned_chart_integrand_support (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (K : Set M) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d)
    (hform : ∀ x, x ∉ K → form.val x = 0) :
    Function.support (unsignedChartIntegrand e form) ⊆ e '' K := by
  intro y hy
  have hyt : y ∈ e.target := by
    by_contra ht
    exact hy (by simp [unsignedChartIntegrand, ht])
  have hx : e.symm y ∈ K := by
    by_contra hx
    have hz := hform (e.symm y) hx
    exact hy (by simp [unsignedChartIntegrand, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart, hz])
  exact ⟨e.symm y, hx, e.right_inv hyt⟩

omit [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] in
theorem unsigned_chart_integral_supported (e : OpenPartialHomeomorph M (Fin d → ℝ))
    (K : Set M) (V : Set (Fin d → ℝ)) (hV : MeasurableSet V) (hVt : V ⊆ e.target)
    (hKV : e '' K ⊆ V) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d)
    (hform : ∀ x, x ∉ K → form.val x = 0) :
    (∫ y in V, form.val.inChart e y (Pi.basisFun ℝ (Fin d))) =
      ∫ y, unsignedChartIntegrand e form y := by
  have hz : ∀ y, y ∉ V → unsignedChartIntegrand e form y = 0 := by
    intro y hy
    apply Function.notMem_support.mp
    intro hs
    exact hy (hKV (unsigned_chart_integrand_support e K form hform hs))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  apply setIntegral_congr_fun hV
  intro y hy
  simp only [unsignedChartIntegrand, LinearMap.coe_mk, AddHom.coe_mk, indicator_of_mem (hVt hy)]

variable [T2Space M] [CompactSpace M]

omit [T2Space M] in
theorem unsigned_chart_integrand_weight_integrable
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ e.source) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    Integrable (unsignedChartIntegrand e (AlgebraicTopology.FundamentalClass.FormPartition.IntegrationConstruction.weightForm ρ hρ form)) := by
  have hc : ContinuousOn (form.val.inChart e) e.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using (form.smooth e he).continuousOn
  have hv := (continuous_eval_const (Pi.basisFun ℝ (Fin d) : Fin d → (Fin d → ℝ))).comp_continuousOn hc
  rw [unsigned_chart_integrand_weight]
  exact (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff_continuous e ρ hρ.continuous hρs _ hv).integrable_of_hasCompactSupport
    (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff_hasCompactSupport e ρ hρs _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnsignedChartIntegral.CM
