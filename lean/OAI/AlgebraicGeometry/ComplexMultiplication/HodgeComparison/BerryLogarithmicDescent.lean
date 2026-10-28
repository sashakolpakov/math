import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LogarithmicPhase
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalHolomorphicLogarithm

/-! # Berry Logarithmic Descent -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryLogarithmicDescent.CM.Construction

noncomputable section

/-! The normalized projective connection has exact logarithmic changes,
and the changes of logarithms have genuine integer defects. -/

open Set
open scoped _root_.Manifold ContDiff

theorem normalizedImaginaryPart_exp_period (z : ℂ) (hz : Complex.exp z = 1) :
    ∃ n : ℤ, LogarithmicPhase.CM.Construction.normalizedImaginaryPart z = (n : ℂ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  refine ⟨n, ?_⟩
  rw [hn, LogarithmicPhase.CM.Construction.normalizedImaginaryPart_apply]
  simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, zero_mul, mul_zero, zero_add, add_zero,
    mul_one, sub_zero]
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [mul_div_cancel_right₀ _ hπ, Complex.ofReal_intCast]

theorem logarithmic_phase_integer_defect (a b c : ℂ)
    (h : Complex.exp a * Complex.exp b = Complex.exp c) :
    ∃ n : ℤ, LogarithmicPhase.CM.Construction.normalizedImaginaryPart a + LogarithmicPhase.CM.Construction.normalizedImaginaryPart b -
      LogarithmicPhase.CM.Construction.normalizedImaginaryPart c = (n : ℂ) := by
  have he : Complex.exp (a + b - c) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, h, div_self (Complex.exp_ne_zero c)]
  simpa only [map_sub, map_add] using normalizedImaginaryPart_exp_period (a + b - c) he

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : Type} [Fintype ι]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def smoothLiftBerry (f : M → ι → ℂ)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f) (hn : ∀ x, f x ≠ 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 :=
  ⟨ManifoldMetric.CM.Construction.manifoldLiftBerry f, ManifoldMetric.CM.Construction.manifoldLiftBerry_smooth isOpen_univ f hf.contMDiffOn (fun x _ => hn x)⟩

theorem smoothLiftBerry_logarithmic_change (f g : M → ι → ℂ) (l : M → ℂ)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ g)
    (hl : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ l)
    (hnf : ∀ x, f x ≠ 0) (hng : ∀ x, g x ≠ 0)
    (hfg : ∀ x, f x = Complex.exp (l x) • g x) :
    smoothLiftBerry f hf hnf - smoothLiftBerry g hg hng =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (LogarithmicPhase.CM.Construction.logarithmicPhasePrimitive l hl) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : x ∈ e.source := mem_chart_source E x
  have hz : e x ∈ e.target := e.map_source hx
  apply ManifoldMetric.CM.Construction.rawManifoldForm_eq_at_of_inChart_eq _ _ e he x hx
  change (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) f - ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) g).inChart e (e x) = _
  ext v
  change (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) f).inChart e (e x) v -
    (ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) g).inChart e (e x) v =
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (LogarithmicPhase.CM.Construction.logarithmicPhasePrimitive l hl)).val.inChart e (e x) v
  rw [LogarithmicPhase.CM.Construction.logarithmicPhasePrimitive_d_inChart l hl e he hz]
  let a : M → ℂ := fun y => Complex.exp (l y)
  have ha : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ a := Complex.contDiff_exp.comp_contMDiff hl
  have hc : ContDiffAt ℂ ∞ (l ∘ e.symm) (e x) :=
    ((hl (e.symm (e x))).comp (e x)
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hz)).contDiffAt
  have hder : fderiv ℂ (a ∘ e.symm) (e x) (v 0) / a (e.symm (e x)) =
      fderiv ℂ (l ∘ e.symm) (e x) (v 0) :=
    BerryGauge.CM.Construction.logarithmic_derivative_of_exp (hc.differentiableAt (by simp)) (v 0)
  have hchange := BerryGauge.CM.Construction.manifoldLiftBerry_gauge_inChart isOpen_univ f g a
    hf.contMDiffOn hg.contMDiffOn ha.contMDiffOn (fun y _ => hng y)
    (fun y _ => Complex.exp_ne_zero (l y)) (fun y _ => hfg y) e he ⟨hz, mem_univ _⟩ v
  rw [hder] at hchange
  exact hchange.trans (LogarithmicPhase.CM.Construction.normalizedImaginaryPart_apply _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryLogarithmicDescent.CM.Construction
