import OAI.AlgebraicGeometry.DivisorClass.Chern.FubiniStudyPositiveMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MetricTwists
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureDomination
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Potential

/-! # Positive Curvature -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PositiveCurvature
open scoped _root_.Manifold
section

/-! Sufficiently large actual holomorphic twists admit the constructed positive metric. -/

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance positiveHolomorphicTwists_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

theorem smoothForm_positive_after_scaled_projective_multiple (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (F : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m → ∀ (x : V.analyticSpace)
      (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      0 < (F x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re +
        (m : ℝ) * c * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  obtain ⟨N, hN, hpos⟩ := Projective.CurvatureDomination.smoothForm_positive_after_projective_multiple V (((c⁻¹ : ℝ) : ℂ) • F)
  refine ⟨N, hN, ?_⟩
  intro m hm x v hv
  have hp := hpos m hm x v hv
  change 0 < (((c⁻¹ : ℝ) : ℂ) * F x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re +
    (m : ℝ) * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re at hp
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  have hp' := mul_pos hc hp
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at hp'
  nlinarith only [hp']

def positiveHolomorphicTwistMetric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ) :
    HolomorphicMetric.Data.HolomorphicLineMetricData (u + n • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) :=
  MetricTwists.holomorphicMetricTwist u (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) h (FubiniStudyPositiveMetric.fubiniStudyTwistMetric V) n

theorem positiveHolomorphicTwistMetric_curvature (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (n : ℕ) :
    Complex.I • (positiveHolomorphicTwistMetric V u h n).curvature =
      Complex.I • h.curvature +
        ((n : ℂ) * (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V : ℂ)) • ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V := by
  rw [positiveHolomorphicTwistMetric, MetricTwists.holomorphicMetricTwist_curvature, smul_add,
    smul_comm Complex.I n, FubiniStudyPositiveMetric.fubiniStudyTwistMetric_real_curvature,
    ← Nat.cast_smul_eq_nsmul ℂ n, smul_smul]

theorem positiveHolomorphicTwistMetric_eventually_positive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ (x : V.analyticSpace)
      (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      0 < ((Complex.I • (positiveHolomorphicTwistMetric V u h n).curvature) x
        ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  obtain ⟨N, hN, hpos⟩ := smoothForm_positive_after_scaled_projective_multiple V
    (Complex.I • h.curvature) (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V)
    (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient_pos V)
  refine ⟨N, hN, ?_⟩
  intro n hn x v hv
  rw [positiveHolomorphicTwistMetric_curvature]
  change 0 < ((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v] +
    ((n : ℂ) * (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V : ℂ)) *
      ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re
  simpa only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    zero_add, sub_zero] using hpos n hn x v hv

end

/-! Actual twisting metrics eventually dominate any prescribed smooth two-form. -/

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance curvatureLowerBounds_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℝ V.analyticModel := FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem positiveHolomorphicTwistMetric_dominates
    (G : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 2) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ (x : V.analyticSpace)
      (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      (G x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re <
        ((Complex.I • (positiveHolomorphicTwistMetric V u h n).curvature) x
          ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  obtain ⟨N, hN, hpos⟩ := smoothForm_positive_after_scaled_projective_multiple V
    (Complex.I • h.curvature - G) (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V)
      (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient_pos V)
  refine ⟨N, hN, ?_⟩
  intro n hn x v hv
  have hp := hpos n hn x v hv
  change 0 < (((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]) -
    G x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re +
      (n : ℝ) * FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V *
        (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re at hp
  rw [Complex.sub_re] at hp
  rw [positiveHolomorphicTwistMetric_curvature]
  change (G x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re <
    ((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v] +
      ((n : ℂ) * (FubiniStudyPositiveMetric.fubiniStudyTwistCurvatureCoefficient V : ℂ)) *
        ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    zero_add, sub_zero]
  linarith only [hp]

theorem positiveHolomorphicTwistMetric_projective_lower_bound (c : ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ (x : V.analyticSpace)
      (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      c * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re <
        ((Complex.I • (positiveHolomorphicTwistMetric V u h n).curvature) x
          ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  obtain ⟨N, hN, hpos⟩ := positiveHolomorphicTwistMetric_dominates V u h ((c : ℂ) • ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V)
  refine ⟨N, hN, ?_⟩
  intro n hn x v hv
  have hp := hpos n hn x v hv
  change ((c : ℂ) * ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re < _ at hp
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hp

end AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PositiveCurvature

namespace AlgebraicGeometry.DivisorClass.Chern

/-! Exact actual curvature evaluation and its lower bound after a real scalar metric potential. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.withPotential_curvature_re
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f)
    (x : V.analyticSpace) (v : Fin 2 → TangentSpace 𝓘(ℝ, V.analyticModel) x) :
    ((Complex.I • (h.withPotential f).curvature) x v).re =
      ((Complex.I • h.curvature) x v).re + ((Complex.I • Projective.ScalarPotential.globalScalarCurvature f) x v).re := by
  rw [h.withPotential_curvature f hf, smul_add]
  exact Complex.add_re _ _

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.withPotential_projective_lower_bound
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) (hf : ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm f = f)
    (c B : ℝ)
    (hb : ∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      (c + B) * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • h.curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re)
    (hfB : ∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      -B * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • Projective.ScalarPotential.globalScalarCurvature f) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re) :
    ∀ (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      c * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • (h.withPotential f).curvature) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re := by
  intro x v hv
  rw [h.withPotential_curvature_re V f hf]
  nlinarith only [hb x v hv, hfB x v hv]

end AlgebraicGeometry.DivisorClass.Chern

end

end OAI
