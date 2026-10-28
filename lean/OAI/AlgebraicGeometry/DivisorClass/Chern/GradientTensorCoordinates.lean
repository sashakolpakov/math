import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Gradient Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoordinates

noncomputable section

/-! Genuine finite Hilbert coordinates for all directional covectors, with exact basis reconstruction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

abbrev CovectorGradientCoordinates (ι : Type) [Fintype ι] (n : ℕ) :=
  PiLp 2 (fun _ : ι => OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)

def covectorGradientComponent (n : ℕ) (i : ι) :
    CovectorGradientCoordinates ι n →L[ℝ] OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n :=
  ((ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)).toContinuousLinearMap)

omit [LinearOrder ι] in
theorem covectorGradientComponent_apply (n : ℕ) (i : ι) (v : CovectorGradientCoordinates ι n) :
    covectorGradientComponent n i v = v i := rfl

def covectorGradientTensor (b : Module.Basis ι ℝ E) (n : ℕ) :
    CovectorGradientCoordinates ι n →L[ℝ] E →L[ℝ] OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  ∑ i, (ContinuousLinearMap.smulRightL ℝ E (OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (b.coord i).toContinuousLinearMap).comp
    (((OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ).comp
      (covectorGradientComponent n i))

theorem covectorGradientTensor_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (v : CovectorGradientCoordinates ι n) (x : E) :
    covectorGradientTensor b n v x = ∑ i, b.repr x i • (OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (v i) := by
  simp only [covectorGradientTensor, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    covectorGradientComponent_apply]
  rfl

theorem covectorGradientTensor_basis (b : Module.Basis ι ℝ E) (n : ℕ)
    (v : CovectorGradientCoordinates ι n) (i : ι) :
    covectorGradientTensor b n v (b i) = (OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (v i) := by
  rw [covectorGradientTensor_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem covectorGradientTensor_injective (b : Module.Basis ι ℝ E) (n : ℕ) :
    Function.Injective (covectorGradientTensor b n) := by
  intro v w h
  apply PiLp.ext
  intro i
  apply (OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.injective
  exact (covectorGradientTensor_basis b n v i).symm.trans
    ((congrArg (fun L : E →L[ℝ] OAI.Analysis.DifferentialForms.Manifold.Basic.FormValue E n => L (b i)) h).trans (covectorGradientTensor_basis b n w i))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoordinates
