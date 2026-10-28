import OAI.Analysis.PDE.Weak.SobolevWeakCompactTest

open Set _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  {μ : Measure X} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

omit [BorelSpace X] [SecondCountableTopology X] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
/-- The real weak derivative identity also holds against complex C¹
test functions when the two pairings are integrable. -/
theorem HasWeakDirectionalDerivative.complex_test_of_compact_support
    {v : X} {u g : X → ℝ} (h : HasWeakDirectionalDerivative μ v u g)
    {K : Set X} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0) (hg : ∀ᵐ x ∂μ, x ∉ K → g x = 0)
    {φ : X → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hgφ : Integrable (fun x ↦ (g x : ℂ) * φ x) μ)
    (huφ : Integrable (fun x ↦ (u x : ℂ) * fderiv ℝ φ x v) μ) :
    (∫ x, (g x : ℂ) * φ x ∂μ) = -(∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ) := by
  have hφd (x : X) : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by norm_num) x).hasFDerivAt
  have hreD (x : X) : fderiv ℝ (fun x ↦ (φ x).re) x v = (fderiv ℝ φ x v).re := by
    exact congrArg (fun L : X →L[ℝ] ℝ ↦ L v)
      ((Complex.reCLM.hasFDerivAt.comp x (hφd x)).fderiv)
  have himD (x : X) : fderiv ℝ (fun x ↦ (φ x).im) x v = (fderiv ℝ φ x v).im := by
    exact congrArg (fun L : X →L[ℝ] ℝ ↦ L v)
      ((Complex.imCLM.hasFDerivAt.comp x (hφd x)).fderiv)
  have hre := h.test_of_compact_support hK hu hg (Complex.reCLM.contDiff.comp hφ)
  have him := h.test_of_compact_support hK hu hg (Complex.imCLM.contDiff.comp hφ)
  apply Complex.ext
  · rw [Complex.neg_re]
    change Complex.reCLM (∫ x, (g x : ℂ) * φ x ∂μ) =
      -Complex.reCLM (∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ)
    rw [← Complex.reCLM.integral_comp_comm hgφ, ← Complex.reCLM.integral_comp_comm huφ]
    simpa [Function.comp_def, hreD, mul_comm] using hre
  · rw [Complex.neg_im]
    change Complex.imCLM (∫ x, (g x : ℂ) * φ x ∂μ) =
      -Complex.imCLM (∫ x, (u x : ℂ) * fderiv ℝ φ x v ∂μ)
    rw [← Complex.imCLM.integral_comp_comm hgφ, ← Complex.imCLM.integral_comp_comm huφ]
    simpa [Function.comp_def, himD, mul_comm] using him

end OAI.Analysis.PDE.Weak
