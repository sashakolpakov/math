import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Logarithmic Connection Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LogarithmicConnectionChange

noncomputable section

/-! An actual local exponential identity determines the difference of
logarithmic derivatives, with no chosen global logarithm. -/

open Filter _root_.Topology

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem logarithmicDerivative_exp_change (f g l : A → ℂ) (x v : A)
    (hf : DifferentiableAt ℂ f x) (hl : DifferentiableAt ℂ l x) (hn : f x ≠ 0)
    (he : g =ᶠ[𝓝 x] (fun y => Complex.exp (l y) * f y)) :
    (g x)⁻¹ * fderiv ℂ g x v - (f x)⁻¹ * fderiv ℂ f x v = fderiv ℂ l x v := by
  have hd := hl.hasFDerivAt.cexp.mul hf.hasFDerivAt
  have hg : fderiv ℂ g x v =
      Complex.exp (l x) * fderiv ℂ f x v +
        f x * (Complex.exp (l x) * fderiv ℂ l x v) :=
    (congrArg (fun d : A →L[ℂ] ℂ => d v) he.fderiv_eq).trans
      (congrArg (fun d : A →L[ℂ] ℂ => d v) hd.fderiv)
  rw [he.eq_of_nhds, hg]
  field_simp [hn, Complex.exp_ne_zero]
  ring

theorem logarithmicDerivative_ratio_log (f g l : A → ℂ) (x v : A)
    (hf : DifferentiableAt ℂ f x) (hl : DifferentiableAt ℂ l x) (hn : f x ≠ 0)
    (he : (fun y => Complex.exp (l y)) =ᶠ[𝓝 x] (fun y => g y / f y)) :
    (g x)⁻¹ * fderiv ℂ g x v - (f x)⁻¹ * fderiv ℂ f x v = fderiv ℂ l x v := by
  apply logarithmicDerivative_exp_change f g l x v hf hl hn
  filter_upwards [he, hf.continuousAt.eventually_ne hn] with y hy hyn
  rw [hy, div_mul_cancel₀ _ hyn]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LogarithmicConnectionChange
