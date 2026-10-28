import OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyTransform
import OAI.AlgebraicGeometry.Comparison.Betti.VectorDbar
import Mathlib.Analysis.Normed.Module.Dual

/-! # Vector Cauchy Right Inverse -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyRightInverse.Dolbeault

noncomputable section

/-! The actual vector-valued Cauchy integral is a right inverse to the
antiholomorphic derivative, proved by continuous complex dual evaluation. -/

open scoped ContDiff

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorDbar_cauchyTransform {f : ℂ → F} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) : VectorDbar.Dolbeault.vectorDbar (VectorCauchyTransform.Dolbeault.vectorCauchyTransform f) z = f z := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro L
  have ht : DifferentiableAt ℝ (VectorCauchyTransform.Dolbeault.vectorCauchyTransform f) z :=
    (VectorCauchyTransform.Dolbeault.vectorCauchyTransform_smooth hc hf).differentiable (by simp) z
  rw [VectorDbar.Dolbeault.vectorDbar_map L ht]
  have he : L ∘ VectorCauchyTransform.Dolbeault.vectorCauchyTransform f = DivisorClass.Chern.CauchyKernel.cauchyTransform (L ∘ f) := by
    funext w
    exact VectorCauchyTransform.Dolbeault.vectorCauchyTransform_map L hc hf.continuous w
  rw [he, VectorDbar.Dolbeault.vectorDbar_scalar]
  exact DivisorClass.Chern.CauchyPolarIntegral.complexDbar_cauchyTransform
    ((L.restrictScalars ℝ).contDiff.comp hf) (hc.comp_left L.map_zero) z

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyRightInverse.Dolbeault
