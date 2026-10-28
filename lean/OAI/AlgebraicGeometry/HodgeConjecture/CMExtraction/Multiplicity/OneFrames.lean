import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMGlobalFrames

/-! # One Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneFrames.Quadratic

noncomputable section

/-! Actual rational and local AdelicSplitting frames for one CM multiplicity line.
The skew coefficient retains the sign and factor two required by the
native rational trace pairing. -/

open scoped Classical
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMGlobalFrames.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)

def singleRealCoefficient : Fin 1 → maximalRealSubfield E :=
  fun _ => ⟨a, (IsCMField.complexConj_eq_self_iff E a).mp ha⟩

include ha0 in
theorem singleRealCoefficient_ne_zero (i : Fin 1) : singleRealCoefficient E a ha i ≠ 0 := by
  intro h
  exact ha0 (congrArg (fun x : maximalRealSubfield E => (x : E)) h)

def singleSkewUnit :
    (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)))ˣ :=
  ThetaCycle.DiagonalFrame.CM.diagonalSkewUnit _ (ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E δ hδ hδ0)
    (singleRealCoefficient E a ha) (singleRealCoefficient_ne_zero E a ha ha0)

theorem singleSkewUnit_conjTranspose :
    (singleSkewUnit E δ hδ hδ0 a ha ha0).val.conjTranspose =
      -(singleSkewUnit E δ hδ hδ0 a ha ha0).val :=
  ThetaCycle.DiagonalFrame.CM.diagonal_skew_conjugateTranspose _ _

def singleGlobalFrames :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (singleSkewUnit E δ hδ hδ0 a ha ha0) :=
  ThetaCycle.GlobalFrames.CM.diagonalGlobalFrames _ _ (ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E δ hδ hδ0)
    (ThetaCycle.UnitaryFrame.CM.realHermitianCoefficients E b hb) (ThetaCycle.CMGlobalFrames.CM.real_hermitian_coefficients_ne_zero E b hb hb0)
    (singleRealCoefficient E a ha) (singleRealCoefficient_ne_zero E a ha ha0)

theorem singleSkewUnit_evaluation (i j : Fin 1) :
    ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0 ((singleSkewUnit E δ hδ hδ0 a ha ha0).val i j) =
      (Matrix.diagonal (fun _ : Fin 1 => -2 * δ * a)) i j := by
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp only [singleSkewUnit, ThetaCycle.DiagonalFrame.CM.diagonalSkewUnit, ThetaCycle.DiagonalFrame.CM.diagonalMatrixUnit, Matrix.diagonal_apply_eq]
  change ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0
    (⟨0, -2 * singleRealCoefficient E a ha i⟩ :
      RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)) = -2 * δ * a
  change ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ _ = -2 * δ * a
  rw [ThetaCycle.QuadraticModel.CM.cm_quadratic_map_apply]
  change (0 : E) + (-2 * a) * δ = -2 * δ * a
  ring

theorem singleGlobalFrames_compatible
    (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield E))
    (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1)
    (i : Fin (3 * 1) ⊕ Fin (3 * 1)) :
    ((singleGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).localFrame v).coordinates
        (fun j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) v (x j)) i =
      RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield E) v
        ((singleGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).rational.coordinates x i) :=
  (singleGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).coordinates_compatible v x i

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneFrames.Quadratic
