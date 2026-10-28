import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Complex.Basic

/-! # Chart Logarithm Differential -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartLogarithmDifferential

noncomputable section

/-! The inverse vertical differential for the literal chart exponential
comes from the complex derivative of the actual multiplication law. -/

open Set Filter
open scoped _root_.Topology _root_.Manifold ContDiff

open OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian

variable {P V E G : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G]

theorem chart_exponential_complex_multiplication_differential
    (c : OpenPartialHomeomorph G V)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hm : ContDiffOn ℂ 1 m D) (p : P)
    (hcomparison : ∀ u w, (p, (u, w)) ∈ D → m (p, (u, w)) = c (c.symm u * c.symm w))
    (v y : V) (hv : ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c v ∈ c.source)
    (hy : c (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c v) = y) (hpoint : (p, (y, (0 : V))) ∈ D) :
    HasFDerivAt (fun w => c (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c w))
      ((fderiv ℂ (fun w => m (p, (y, w))) 0).restrictScalars ℝ) v := by
  have hn := ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponentialCoordinates_hasFDerivAt c hc h1 h0 v hv
  rw [hy] at hn
  have heq : (fun w => m (p, (y, w))) =ᶠ[𝓝 (0 : V)]
      (fun w => c (c.symm y * c.symm w)) := by
    have hmem := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
      |>.preimage_mem_nhds (hD.mem_nhds hpoint)
    filter_upwards [hmem] with w hw
    exact hcomparison y w hw
  have hf : DifferentiableAt ℂ (fun w => m (p, (y, w))) (0 : V) :=
    ((hm.contDiffAt (hD.mem_nhds hpoint)).comp 0
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by norm_num)
  exact hn.congr_fderiv (heq.fderiv_eq.symm.trans (hf.hasFDerivAt.restrictScalars ℝ).fderiv)

omit [NormedSpace ℂ P] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] [T2Space G] in
theorem multiplication_differential_at_identity
    (c : OpenPartialHomeomorph G V) (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D) (p : P)
    (hcomparison : ∀ u w, (p, (u, w)) ∈ D → m (p, (u, w)) = c (c.symm u * c.symm w))
    (hpoint : (p, ((0 : V), 0)) ∈ D) :
    fderiv ℂ (fun w => m (p, (0, w))) 0 = ContinuousLinearMap.id ℂ V := by
  have hz : (0 : V) ∈ c.target := h0 ▸ c.map_source h1
  have hi : c.symm 0 = (1 : G) := by rw [← h0, c.left_inv h1]
  have heq : (fun w => m (p, (0, w))) =ᶠ[𝓝 (0 : V)] id := by
    have hmem := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
      |>.preimage_mem_nhds (hD.mem_nhds hpoint)
    filter_upwards [hmem, c.open_target.mem_nhds hz] with w hw hwt
    rw [hcomparison 0 w hw, hi, one_mul, c.right_inv hwt]
    rfl
  rw [heq.fderiv_eq]
  exact fderiv_id

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartLogarithmDifferential
