import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorReconstruction

/-! # Tensor Gradient Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorGradientCoordinates

noncomputable section

/-! Coordinate extraction is the continuous inverse of the literal gradient tensor reconstruction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def covectorTensorGradientCoordinates (b : Module.Basis ι ℝ E) (n : ℕ) :
    (E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates ι n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (b i))))

theorem covectorTensorGradientCoordinates_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorTensorGradientCoordinates b n L = WithLp.toLp 2 (fun i => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L (b i))) := rfl

theorem covectorGradientTensor_left_inverse (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    GradientTensorCoordinates.covectorGradientTensor b n (covectorTensorGradientCoordinates b n L) = L :=
  GradientTensorReconstruction.covectorGradientTensor_reconstruction b n L

theorem covectorGradientTensor_right_inverse (b : Module.Basis ι ℝ E) (n : ℕ)
    (v : GradientTensorCoordinates.CovectorGradientCoordinates ι n) :
    covectorTensorGradientCoordinates b n (GradientTensorCoordinates.covectorGradientTensor b n v) = v := by
  apply GradientTensorCoordinates.covectorGradientTensor_injective b n
  exact covectorGradientTensor_left_inverse b n _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorGradientCoordinates
