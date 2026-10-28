import Mathlib

/-! A generic dominated-differentiation lemma, independent of matrix norm instances. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open _root_.MeasureTheory
open scoped Topology

theorem integral_fderiv_linear_zero
    {E F Z α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace α]
    {μ : Measure α} (A : E → α → F) {x : E} {s : Set E} (hs : s ∈ 𝓝 x)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (A y) μ) (hA : Integrable (A x) μ)
    (hDmeas : AEStronglyMeasurable (fun t => fderiv ℝ (fun y => A y t) x) μ)
    (hD : ∀ᵐ t ∂μ, ∀ y ∈ s, DifferentiableAt ℝ (fun z => A z t) y)
    (hDbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖fderiv ℝ (fun z => A z t) y‖ ≤ bound t)
    (L : (E →L[ℝ] F) →L[ℝ] Z)
    (hzero : ∀ᵐ t ∂μ, L (fderiv ℝ (fun y => A y t) x) = 0) :
    L (fderiv ℝ (fun y => ∫ t, A y t ∂μ) x) = 0 := by
  have hDiff := hasFDerivAt_integral_of_dominated_of_fderiv_le hs hmeas hA hDmeas
    hDbound hbound (hD.mono fun _ ht y hy => (ht y hy).hasFDerivAt)
  have hDint : Integrable (fun t => fderiv ℝ (fun y => A y t) x) μ :=
    hbound.mono' hDmeas (hDbound.mono fun _ ht => ht x (mem_of_mem_nhds hs))
  rw [hDiff.fderiv, ← L.integral_comp_comm hDint]
  simpa using integral_congr_ae hzero

end OAI.Analysis.Calculus.Quaternion
