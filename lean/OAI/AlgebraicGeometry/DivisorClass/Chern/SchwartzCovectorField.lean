import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorGradientCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.VectorGradientNormalization

/-! # Schwartz Covector Field -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorField

noncomputable section

/-! Literal covector fields of Schwartz coordinate tests and their exact normalized Sobolev gradients. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def schwartzCovectorField (b : Module.Basis ι ℝ E) (n : ℕ) (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  fun z => (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (q z)

theorem schwartzCovectorField_coordinates (b : Module.Basis ι ℝ E) (n : ℕ)
    (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) (z : E) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (schwartzCovectorField b n q z) = q z :=
  (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).apply_symm_apply _

theorem schwartzCovectorField_smooth (b : Module.Basis ι ℝ E) (n : ℕ)
    (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) : ContDiff ℝ ∞ (schwartzCovectorField b n q) :=
  ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (q.smooth ⊤)

theorem schwartzCovectorField_tsupport (b : Module.Basis ι ℝ E) (n : ℕ)
    (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) : tsupport (schwartzCovectorField b n q) ⊆ tsupport q :=
  tsupport_comp_subset (g := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm) (map_zero _) q

theorem schwartzCovectorField_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) (z v : E) :
    fderiv ℝ q z v = Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (fderiv ℝ (schwartzCovectorField b n q) z v) := by
  let L := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ
  have heq : (q : E → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) = fun y => L (schwartzCovectorField b n q y) :=
    funext (fun y => (schwartzCovectorField_coordinates b n q y).symm)
  have hd := (L.hasFDerivAt.comp z ((schwartzCovectorField_smooth b n q).differentiable (by simp) z).hasFDerivAt).fderiv
  exact (congrArg (fun p => fderiv ℝ p z v) heq).trans (congrArg (fun T => T v) hd)

theorem schwartzCovectorField_normalized_gradient [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) (n : ℕ) (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) :
    ∀ᵐ z ∂(volume : Measure E),
      (2 * Real.pi * Complex.I : ℂ) • Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) b (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) z =
        TensorGradientCoordinates.covectorTensorGradientCoordinates b.toBasis n (fderiv ℝ (schwartzCovectorField b.toBasis n q) z) := by
  apply (VectorGradientNormalization.vectorGradient_physical_schwartz b q).mono
  intro z hz
  exact hz.trans (PiLp.ext (fun j => schwartzCovectorField_derivative b.toBasis n q z (b j)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorField
