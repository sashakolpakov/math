import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyPolarIntegral

/-! # Vector Dbar -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorDbar.Dolbeault

noncomputable section

/-! The actual antiholomorphic directional derivative for vector-valued
functions and its naturality under continuous complex-linear maps. -/

open _root_.ContinuousLinearMap

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]

def vectorDbar (f : ℂ → F) (z : ℂ) : F :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM ℂ F (fderiv ℝ f z) 1

theorem vectorDbar_map (L : F →L[ℂ] G) {f : ℂ → F} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) : L (vectorDbar f z) = vectorDbar (L ∘ f) z := by
  have hd : fderiv ℝ (L ∘ f) z = (L.restrictScalars ℝ).comp (fderiv ℝ f z) :=
    ((L.restrictScalars ℝ).hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  simp only [vectorDbar, hd, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, map_smul, map_add,
    ContinuousLinearMap.comp_apply]
  rfl

theorem vectorDbar_scalar (f : ℂ → ℂ) (z : ℂ) : vectorDbar f z = DivisorClass.Chern.CauchyPolarCalculus.complexDbar f z := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorDbar.Dolbeault
