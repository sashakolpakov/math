import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.DualChartDifferences

/-! # Chart Difference Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartDifferenceCoefficients

noncomputable section

/-! The native derivation of a product-chart transition evaluates to
the difference of the two original second coefficients. -/

open scoped TensorProduct

variable {k A P : Type*} [CommRing k] [CommRing A] [CommRing P]
    [Algebra k A] [Algebra (DualNumber k) P]

local instance productDifferenceCoefficients_commRing : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem dualProductChartDifference_coefficients (q : P →+* A)
    (f g : P ≃ₐ[DualNumber k] (DualNumber k ⊗[k] A))
    (hf : ∀ p, Dual.TensorReduction.dualTensorReduction k A (f p) = q p)
    (hg : ∀ p, Dual.TensorReduction.dualTensorReduction k A (g p) = q p) (p : P) :
    Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg (q p) =
      (Dual.NumberCoefficients.dualTensorCoefficientEquiv k A (g p)).snd - (Dual.NumberCoefficients.dualTensorCoefficientEquiv k A (f p)).snd := by
  let C := Dual.NumberCoefficients.dualTensorCoefficientEquiv k A
  let e := Smooth.DualChartDifferences.dualProductChartTransition f g
  let he := Smooth.DualChartDifferences.dualProductChartTransition_reduction q f g hf hg
  have H := congrArg TrivSqZeroExt.snd
    (Dual.Derivation.dualReductionIdentity_normalForm (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates e).toAlgHom
      (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_reduction e he) (Dual.CoefficientLiftTensorMap.dualTensorTransitionCoordinates_eps e) (C (f p)))
  change (C (g (f.symm (C.symm (C (f p)))))).snd =
    Smooth.DualChartDifferences.dualProductChartDifference q f g hf hg (C (f p)).fst + (C (f p)).snd at H
  rw [C.symm_apply_apply, f.symm_apply_apply] at H
  have hq : (C (f p)).fst = q p := hf p
  rw [hq] at H
  exact (eq_sub_iff_add_eq).mpr H.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ChartDifferenceCoefficients
