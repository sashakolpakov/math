import OAI.AlgebraicGeometry.Comparison.Betti.VectorDbar
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Vector Dbar Holomorphic Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorDbarHolomorphicPullback.Dolbeault

noncomputable section

/-! The actual antiholomorphic derivative under a holomorphic change
of the complex-line variable, including the inversion Jacobian. -/

variable {E G F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem complexAntilinearPart_precompose (D : G →L[ℝ] F) (L : E →L[ℂ] G) (v : E) :
    OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F (D.comp (L.restrictScalars ℝ)) v =
      OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM G F D (L v) := by
  rw [OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  change (1 / 2 : ℂ) • (D (L v) + Complex.I • D (L (Complex.I • v))) = _
  rw [map_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] in
theorem vectorDbar_comp_holomorphic {f : ℂ → F} {φ : ℂ → ℂ} {z a : ℂ}
    (hf : DifferentiableAt ℝ f (φ z)) (hφ : HasDerivAt φ a z) :
    VectorDbar.Dolbeault.vectorDbar (f ∘ φ) z = star a • VectorDbar.Dolbeault.vectorDbar f (φ z) := by
  have hd := (hf.hasFDerivAt.comp z (hφ.hasFDerivAt.restrictScalars ℝ)).fderiv
  rw [VectorDbar.Dolbeault.vectorDbar, hd, complexAntilinearPart_precompose]
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one, one_mul, VectorDbar.Dolbeault.vectorDbar] using
    OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul ℂ F (fderiv ℝ f (φ z)) a 1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G] in
theorem vectorDbar_comp_inv {f : ℂ → F} {z : ℂ}
    (hf : DifferentiableAt ℝ f z⁻¹) (hz : z ≠ 0) :
    VectorDbar.Dolbeault.vectorDbar (fun w => f w⁻¹) z = star (-(z ^ 2)⁻¹) • VectorDbar.Dolbeault.vectorDbar f z⁻¹ :=
  vectorDbar_comp_holomorphic hf (hasDerivAt_inv hz)

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorDbarHolomorphicPullback.Dolbeault
