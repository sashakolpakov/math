import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AntiholomorphicDivergence
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm

/-! # Holomorphic Integration By Parts -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

noncomputable section

section

/-! Integration by parts for actual complex directional derivatives and
compactly supported smooth scalar tests. -/

open _root_.MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem smooth_mul_compact_integrable (w g : E → ℂ)
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    Integrable (fun x => w x * g x) μ :=
  (hw.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left

theorem integral_mul_directional (w g : E → ℂ)
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (u : E) :
    (∫ x, w x * fderiv ℝ g x u ∂μ) = -(∫ x, fderiv ℝ w x u * g x ∂μ) :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (smooth_mul_compact_integrable μ _ g (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative w hw u) hg hgc)
    (smooth_mul_compact_integrable μ w _ hw (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg u)
      (hgc.fderiv_apply ℝ u))
    (smooth_mul_compact_integrable μ w g hw hg hgc)
    (fun x _ => (hw.differentiable (by simp)).differentiableAt)
    (fun x _ => (hg.differentiable (by simp)).differentiableAt)

variable [NormedSpace ℂ E]

theorem integral_mul_holomorphicDirectionalDerivative (w g : E → ℂ)
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (u : E) :
    (∫ x, w x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u ∂μ) =
      -(∫ x, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative w x u * g x ∂μ) := by
  have hL (v : E) := smooth_mul_compact_integrable μ w _ hw
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg v) (hgc.fderiv_apply ℝ v)
  have hR (v : E) := smooth_mul_compact_integrable μ _ g
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative w hw v) hg hgc
  have hLf (x : E) : w x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u =
      (1 / 2 : ℂ) * (w x * fderiv ℝ g x u - Complex.I * (w x * fderiv ℝ g x (Complex.I • u))) := by
    rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
    ring
  have hRf (x : E) : MetricDerivative.CM.Construction.holomorphicDirectionalDerivative w x u * g x =
      (1 / 2 : ℂ) * (fderiv ℝ w x u * g x - Complex.I * (fderiv ℝ w x (Complex.I • u) * g x)) := by
    rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
    ring
  simp_rw [hLf, hRf]
  rw [integral_const_mul, integral_const_mul,
    integral_sub (hL u) ((hL (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    integral_sub (hR u) ((hR (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    integral_mul_directional μ w g hw hg hgc u,
    integral_mul_directional μ w g hw hg hgc (Complex.I • u)]
  ring

end

/-! Holomorphic integration by parts for coefficients smooth only on the
actual chart domain; compact test support removes every boundary term. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_mul_test (w g : E → ℂ) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ U) :
    ContDiff ℝ ∞ (fun x => w x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact (hw.contDiffAt (hU.mem_nhds hx)).mul hg.contDiffAt
  · have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    rw [hy, Pi.zero_apply, mul_zero]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem smooth_mul_test_integrable (w g : E → ℂ) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) :
    Integrable (fun x => w x * g x) μ :=
  (smooth_mul_test w g hU hw hg hs).continuous.integrable_of_hasCompactSupport hgc.mul_left

theorem integral_mul_directional_on (w g : E → ℂ) {U : Set E} (hU : IsOpen U)
    (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    (∫ x, w x * fderiv ℝ g x u ∂μ) = -(∫ x, fderiv ℝ w x u * g x ∂μ) :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (smooth_mul_test_integrable μ _ g hU (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw u) hg hgc hs)
    (smooth_mul_test_integrable μ w _ hU hw (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg u)
      (hgc.fderiv_apply ℝ u) ((tsupport_fderiv_apply_subset ℝ u).trans hs))
    (smooth_mul_test_integrable μ w g hU hw hg hgc hs)
    (fun x hx => (hw.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt (by simp))
    (fun x _ => (hg.differentiable (by simp)).differentiableAt)

variable [NormedSpace ℂ E]

theorem integral_mul_holomorphicDirectionalDerivative_on (w g : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hw : ContDiffOn ℝ ∞ w U) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hs : tsupport g ⊆ U) (u : E) :
    (∫ x, w x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u ∂μ) =
      -(∫ x, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative w x u * g x ∂μ) := by
  have hL (v : E) := smooth_mul_test_integrable μ w _ hU hw
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative g hg v) (hgc.fderiv_apply ℝ v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have hR (v : E) := smooth_mul_test_integrable μ _ g hU
    (Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smoothOn_directional_derivative w hU hw v) hg hgc hs
  have hLf (x : E) : w x * MetricDerivative.CM.Construction.holomorphicDirectionalDerivative g x u =
      (1 / 2 : ℂ) * (w x * fderiv ℝ g x u - Complex.I * (w x * fderiv ℝ g x (Complex.I • u))) := by
    rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
    ring
  have hRf (x : E) : MetricDerivative.CM.Construction.holomorphicDirectionalDerivative w x u * g x =
      (1 / 2 : ℂ) * (fderiv ℝ w x u * g x - Complex.I * (fderiv ℝ w x (Complex.I • u) * g x)) := by
    rw [MetricDerivative.CM.Construction.holomorphicDirectionalDerivative]
    ring
  simp_rw [hLf, hRf]
  rw [integral_const_mul, integral_const_mul,
    integral_sub (hL u) ((hL (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    integral_sub (hR u) ((hR (Complex.I • u)).const_mul Complex.I), integral_const_mul,
    integral_mul_directional_on μ w g hU hw hg hgc hs u,
    integral_mul_directional_on μ w g hU hw hg hgc hs (Complex.I • u)]
  ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction
