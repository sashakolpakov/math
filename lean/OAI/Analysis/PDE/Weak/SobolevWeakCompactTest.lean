import OAI.Analysis.PDE.Weak.Elliptic.Derivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {μ : Measure X} [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ]

omit [BorelSpace X] [SecondCountableTopology X] [CompleteSpace V] [μ.IsAddRightInvariant] [IsLocallyFiniteMeasure μ] in
/-- Compactly supported weak data can be tested against any C¹ function:
the cutoff is identically one in a neighborhood of their common support. -/
theorem HasWeakDirectionalDerivative.test_of_compact_support
    {v : X} {u g : X → V} (h : HasWeakDirectionalDerivative μ v u g)
    {K : Set X} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0) (hg : ∀ᵐ x ∂μ, x ∉ K → g x = 0)
    {φ : X → V} (hφ : ContDiff ℝ 1 φ) :
    (∫ x, inner ℝ (g x) (φ x) ∂μ) =
      -(∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ) := by
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_lt
  let χ : ContDiffBump (0 : X) := ⟨R, R + 1, hR, by linarith⟩
  let ψ : X → V := fun x ↦ χ x • φ x
  have hψ : ContDiff ℝ 1 ψ := χ.contDiff.smul hφ
  have hψs : HasCompactSupport ψ := χ.hasCompactSupport.smul_right
  have hlocal (x : X) (hx : x ∈ K) : ψ =ᶠ[𝓝 x] φ := by
    have hb : x ∈ Metric.ball (0 : X) χ.rIn := by
      simpa only [Metric.mem_ball, dist_zero_right, χ] using hRK x hx
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hb] with y hy
    simp only [ψ, hy, Pi.one_apply, one_smul]
  have hleft : (∫ x, inner ℝ (g x) (ψ x) ∂μ) =
      ∫ x, inner ℝ (g x) (φ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    by_cases hxK : x ∈ K
    · rw [(hlocal x hxK).eq_of_nhds]
    · simp only [hx hxK, inner_zero_left]
  have hright : (∫ x, inner ℝ (u x) (fderiv ℝ ψ x v) ∂μ) =
      ∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    by_cases hxK : x ∈ K
    · rw [(hlocal x hxK).fderiv_eq]
    · simp only [hx hxK, inner_zero_left]
  rw [← hleft, ← hright]
  exact h ψ hψ hψs

end OAI.Analysis.PDE.Weak
