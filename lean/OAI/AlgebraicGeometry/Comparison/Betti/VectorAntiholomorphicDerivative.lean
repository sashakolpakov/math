import OAI.AlgebraicGeometry.Comparison.Betti.VectorDbar
import OAI.AlgebraicGeometry.Comparison.Betti.AntilinearCoefficientMap

/-! # Vector Antiholomorphic Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorAntiholomorphicDerivative.Dolbeault

noncomputable section

/-! Actual antiholomorphic directional derivatives of vector-valued
functions, including coefficient naturality and product slices. -/

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]

def vectorAntiDerivative (f : E → F) (x v : E) : F :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F (fderiv ℝ f x) v

theorem vectorAntiDerivative_map (L : F →L[ℂ] G) {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    vectorAntiDerivative (fun y => L (f y)) x v = L (vectorAntiDerivative f x v) := by
  have hd : fderiv ℝ (fun y => L (f y)) x =
      (L.restrictScalars ℝ) ∘L fderiv ℝ f x :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  unfold vectorAntiDerivative
  rw [hd, AntilinearCoefficientMap.Dolbeault.complexAntilinearPart_comp_coefficients]
  rfl

theorem vectorAntiDerivative_eq_zero_iff (f : E → F) (x v : E) :
    vectorAntiDerivative f x v = 0 ↔
      fderiv ℝ f x (Complex.I • v) = Complex.I • fderiv ℝ f x v := by
  unfold vectorAntiDerivative
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, smul_eq_zero,
    or_iff_right (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  constructor
  · intro h
    have hh := congrArg (fun a : F => (-Complex.I) • a) h
    simp only [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, smul_zero] at hh
    simpa only [neg_smul, neg_neg] using eq_neg_of_add_eq_zero_right hh
  · intro h
    rw [h, smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel]

theorem vectorDbar_product_slice {f : E × ℂ → F} {p : E} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) :
    VectorDbar.Dolbeault.vectorDbar (fun z => f (p, z)) w = vectorAntiDerivative f (p, w) (0, 1) := by
  have hd : fderiv ℝ (fun z => f (p, z)) w =
      fderiv ℝ f (p, w) ∘L ContinuousLinearMap.inr ℝ E ℂ :=
    (hf.hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℝ) p w)).fderiv
  unfold VectorDbar.Dolbeault.vectorDbar vectorAntiDerivative
  rw [hd]
  simp only [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorAntiholomorphicDerivative.Dolbeault
