import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarDolbeaultCommutation
import OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyLocalPrimitive

/-! # Product Dolbeault Derivatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDolbeaultDerivatives

noncomputable section

/-! The actual scalar Dolbeault derivatives agree with their product-coordinate slices. -/

open _root_.Complex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem fderiv_product_slice_left {f : P × ℂ → ℂ} {p : P} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) (v : P) :
    fderiv ℝ (fun q => f (q, w)) p v = fderiv ℝ f (p, w) (v, 0) := by
  have h := (hf.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p w)).fderiv
  exact congrArg (fun D : P →L[ℝ] ℂ => D v) h

theorem fderiv_product_slice_right {f : P × ℂ → ℂ} {p : P} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) (v : ℂ) :
    fderiv ℝ (fun z => f (p, z)) w v = fderiv ℝ f (p, w) (0, v) := by
  have h := (hf.hasFDerivAt.comp w (hasFDerivAt_prodMk_right (𝕜 := ℝ) p w)).fderiv
  exact congrArg (fun D : ℂ →L[ℝ] ℂ => D v) h

variable [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P]

theorem antilinearScalarDerivative_product_slice_left {f : P × ℂ → ℂ} {p : P} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) (v : P) :
    AntiOneFormCoordinates.antilinearScalarDerivative (fun q => f (q, w)) p v =
      AntiOneFormCoordinates.antilinearScalarDerivative f (p, w) (v, 0) := by
  change (1 / 2 : ℂ) *
    (fderiv ℝ (fun q => f (q, w)) p v + I * fderiv ℝ (fun q => f (q, w)) p (I • v)) = _
  rw [fderiv_product_slice_left hf, fderiv_product_slice_left hf]
  simp only [AntiOneFormCoordinates.antilinearScalarDerivative, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, Prod.smul_mk,
    smul_eq_mul, mul_zero]

theorem antilinearScalarDerivative_product_slice_right {f : P × ℂ → ℂ} {p : P} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) (v : ℂ) :
    AntiOneFormCoordinates.antilinearScalarDerivative (fun z => f (p, z)) w v =
      AntiOneFormCoordinates.antilinearScalarDerivative f (p, w) (0, v) := by
  change (1 / 2 : ℂ) *
    (fderiv ℝ (fun z => f (p, z)) w v + I * fderiv ℝ (fun z => f (p, z)) w (I • v)) = _
  rw [fderiv_product_slice_right hf, fderiv_product_slice_right hf]
  simp only [AntiOneFormCoordinates.antilinearScalarDerivative, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, Prod.smul_mk,
    smul_zero, smul_eq_mul]

theorem complexDbar_product_slice {f : P × ℂ → ℂ} {p : P} {w : ℂ}
    (hf : DifferentiableAt ℝ f (p, w)) :
    CauchyPolarCalculus.complexDbar (fun z => f (p, z)) w = AntiOneFormCoordinates.antilinearScalarDerivative f (p, w) (0, 1) :=
  antilinearScalarDerivative_product_slice_right hf 1

theorem antilinearScalarDerivative_eq_zero_iff (f : P → ℂ) (x v : P) :
    AntiOneFormCoordinates.antilinearScalarDerivative f x v = 0 ↔ fderiv ℝ f x (I • v) = I * fderiv ℝ f x v := by
  change (1 / 2 : ℂ) * (fderiv ℝ f x v + I * fderiv ℝ f x (I • v)) = 0 ↔ _
  rw [mul_eq_zero, or_iff_right (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  constructor
  · intro h
    calc
      fderiv ℝ f x (I • v) =
          (-I) * (fderiv ℝ f x v + I * fderiv ℝ f x (I • v)) + I * fderiv ℝ f x v := by
        ring_nf
        simp
      _ = I * fderiv ℝ f x v := by rw [h, mul_zero, zero_add]
  · intro h
    rw [h, ← mul_assoc, I_mul_I, neg_one_mul, add_neg_cancel]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDolbeaultDerivatives
