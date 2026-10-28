import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality

/-! # Multiplication -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Multiplication.Constructions

noncomputable section

/-! Bounded smooth scalar localization of genuine manifold L² forms. -/

open scoped ContDiff _root_.Manifold
open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)

theorem projectiveFormPointPair_function_self
    (a : DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace n) (f : V.analyticSpace → ℂ)
    (x : V.analyticSpace) :
    (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a)
      (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a) x).re =
      ‖f x‖ ^ 2 * (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a a x).re := by
  have h := LocalMetric.Constructions.projectiveFormPointPair_congr_at V n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a)
    (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a) (f x • a) (f x • a) x rfl rfl
  rw [h, Form.Constructions.projectiveFormPointPair_smul_left, AdjointManifold.Constructions.projectiveFormPointPair_smul_right, ← mul_assoc,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveL2Pair_function_bound
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    (Form.Constructions.projectiveL2Pair V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)
      (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)).re ≤ C ^ 2 * (Form.Constructions.projectiveL2Pair V n a a).re := by
  let fa := DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a
  have haInt := Complex.reCLM.integrable_comp (Form.Constructions.projectiveFormPointPair_integrable V n a a)
  have hfInt := Complex.reCLM.integrable_comp (Form.Constructions.projectiveFormPointPair_integrable V n fa fa)
  have hpoint (x : V.analyticSpace) : (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n fa.val fa.val x).re ≤
      C ^ 2 * (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n a.val a.val x).re := by
    change (ProjectiveFormMetric.Constructions.projectiveFormPointPair V n (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a.val)
      (DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f a.val) x).re ≤ _
    rw [projectiveFormPointPair_function_self]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hbound x))
      (ProjectiveFormMetric.Constructions.projectiveFormPointPair_nonneg V n a.val x)
  have hInt := integral_mono hfInt (haInt.const_mul (C ^ 2)) hpoint
  rw [integral_const_mul] at hInt
  have hra := integral_re (Form.Constructions.projectiveFormPointPair_integrable V n a a)
  have hrf := integral_re (Form.Constructions.projectiveFormPointPair_integrable V n fa fa)
  exact hrf.symm.le.trans (hInt.trans_eq (congrArg (fun r : ℝ => C ^ 2 * r) hra))

theorem smoothToProjectiveL2_function_norm_bound
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    ‖Form.Constructions.smoothToProjectiveL2 V n (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f hf a)‖ ≤
      C * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
    Form.Constructions.smoothToProjectiveL2_inner, Form.Constructions.smoothToProjectiveL2_inner]
  exact projectiveL2Pair_function_bound V n f hf C hC hbound a

end

end OAI.Analysis.HodgeTheory.Decomposition.Multiplication.Constructions
