import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionAdelicData
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.SplitImage
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalHermitianMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalSplitImage

/-! # Quaternion Active Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionActiveImage.Approximation

noncomputable section

section

/-! The actual local quaternion subgroup fills the binary block of the
native active SL3 factor selected by the given CM embedding. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

theorem cmQuaternion_active_binary_image (A : Matrix.SpecialLinearGroup (Fin 2) (Padic q)) :
    ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup
        (QuadraticCoordinates.squareParameter E δ hδ) (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) (.inr (ActivePlace.Approximation.cmActivePlace E σ)),
      ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (Quaternion.HermitianAdeles.quaternionLocalHermitian (maximalRealSubfield E)
          (QuadraticCoordinates.squareParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)
          (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
          (QuaternionAdelicData.cmHermitianUnit_scalar_diagonal E b hb hb0 δ hδ hδ0) (ActivePlace.Approximation.cmActivePlace E σ) g) =
      Quaternion.QuadraticUnitary.activeBinaryBlock A := by
  have hbF : Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb ≠ 0 := by
    intro h
    exact hb0 (congrArg (fun x : maximalRealSubfield E => (x : E)) h)
  apply Quaternion.LocalSplitImage.quaternionLocalHermitian_split_image (maximalRealSubfield E)
    (QuadraticCoordinates.squareParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (QuaternionAdelicData.cmHermitianUnit_scalar_diagonal E b hb hb0 δ hδ hδ0)
    (ActivePlace.Approximation.cmActivePlace E σ) (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
    (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0) (ActivePlace.Approximation.cmActiveCompletion E σ)
    (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)).toMonoidHom
    ?_ hbF A
  intro g
  exact ActiveProjection.Approximation.cmActiveSL_matrix E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) g

end

/-! Use the CM presentation parameter literally in both the quaternion
approximation theorem and the local Hermitian image theorem. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

include hδ0 in
theorem cmHermitianUnit_cm_scalar :
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val =
      UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap (maximalRealSubfield E)
        (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) :=
  QuaternionAdelicData.cmHermitianUnit_scalar_diagonal E b hb hb0 δ hδ hδ0

theorem cmQuaternion_canonical_image {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
    (A : Matrix.SpecialLinearGroup (Fin 2) (Padic q)) :
    ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup
        (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) (.inr (ActivePlace.Approximation.cmActivePlace E σ)),
      ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (Quaternion.HermitianAdeles.quaternionLocalHermitian (maximalRealSubfield E)
          (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)
          (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
          (cmHermitianUnit_cm_scalar E b hb hb0 δ hδ hδ0) (ActivePlace.Approximation.cmActivePlace E σ) g) =
      Quaternion.QuadraticUnitary.activeBinaryBlock A := by
  have hbF : Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb ≠ 0 := by
    intro h
    exact hb0 (congrArg (fun x : maximalRealSubfield E => (x : E)) h)
  apply Quaternion.LocalSplitImage.quaternionLocalHermitian_split_image (maximalRealSubfield E)
    (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (cmHermitianUnit_cm_scalar E b hb hb0 δ hδ hδ0)
    (ActivePlace.Approximation.cmActivePlace E σ) (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
    (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0) (ActivePlace.Approximation.cmActiveCompletion E σ)
    (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)).toMonoidHom
    (fun g => ActiveProjection.Approximation.cmActiveSL_matrix E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) g) hbF A

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionActiveImage.Approximation
