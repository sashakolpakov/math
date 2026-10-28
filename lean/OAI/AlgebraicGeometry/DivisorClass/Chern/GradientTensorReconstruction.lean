import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoordinates

/-! # Gradient Tensor Reconstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorReconstruction

noncomputable section

/-! The finite gradient coordinates reconstruct the literal directional derivative tensor. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorGradientTensor_reconstruction (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    GradientTensorCoordinates.covectorGradientTensor b n (WithLp.toLp 2 (fun i => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L (b i)))) = L := by
  apply ContinuousLinearMap.ext
  intro x
  rw [GradientTensorCoordinates.covectorGradientTensor_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  have h := congrArg L (b.sum_repr x)
  simpa only [map_sum, map_smul] using h

theorem covectorGradientTensor_eq_of_coefficients (b : Module.Basis ι ℝ E) (n : ℕ)
    (v : GradientTensorCoordinates.CovectorGradientCoordinates ι n) (L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hv : ∀ i, v i = Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L (b i))) : GradientTensorCoordinates.covectorGradientTensor b n v = L := by
  have h : v = WithLp.toLp 2 (fun i => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L (b i))) := PiLp.ext hv
  exact (congrArg (GradientTensorCoordinates.covectorGradientTensor b n) h).trans (covectorGradientTensor_reconstruction b n L)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorReconstruction
