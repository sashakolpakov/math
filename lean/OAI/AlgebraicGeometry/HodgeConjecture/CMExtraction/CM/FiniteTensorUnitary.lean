import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary

/-! # Finite Tensor Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteTensorUnitary.Approximation

noncomputable section

/-! The actual finite unitary restricted product maps continuously to
unitary matrices over the PEL coefficient algebra, with the prescribed
rational CM matrices unchanged. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar.TestTransport OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

abbrev cmCompletedCoefficient :=
  QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0)

theorem cmCompletedCoefficient_star (x) :
    cmCompletedCoefficient E δ hδ hδ0 (star x) =
      star (cmCompletedCoefficient E δ hδ hδ0 x) :=
  QuadraticTensorStar.TestTransport.quadraticAdelicTensorMap_star _ _ (ThetaCycle.QuadraticModel.CM.cm_quadratic_map_star E δ hδ) x

variable (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

theorem cmCompletedHermitianMatrix :
    (Finite.UnitaryDet.Approximation.finiteHermitianMatrix (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)).map
      (cmCompletedCoefficient E δ hδ hδ0) = UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E b) := by
  rw [Finite.UnitaryDet.Approximation.finiteHermitianMatrix, Multiplicity.OneUnitary.Quadratic.cmHermitianUnit_diagonal E δ hδ hδ0,
    Quaternion.LocalUnitary.diagonalForm_map, Quaternion.LocalUnitary.diagonalForm_map]
  congr 1
  exact (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational _ _ _).trans
    (congrArg (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E) ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).apply_symm_apply b))

def cmFiniteTensorUnitary :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) →ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E b)) :=
  (⟨(UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (cmCompletedHermitianMatrix E δ hδ hδ0 b hb hb0)).toMonoidHom,
    Quaternion.LocalUnitary.unitaryFormCongr_continuous _ _ (cmCompletedHermitianMatrix E δ hδ hδ0 b hb hb0)⟩ :
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU _ →ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU _).comp
    ((SpecialUnitaryBaseChange.Approximation.specialUnitaryBaseChangeContinuous (cmCompletedCoefficient E δ hδ hδ0)
      (cmCompletedCoefficient_star E δ hδ hδ0) _
      (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous _ _)).comp
      (Finite.UnitaryDet.Approximation.finiteAdelicUnitary (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)))

theorem cmFiniteTensorUnitary_matrix
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)) :
    (cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0 g).val.val =
      (Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) g).map
        (cmCompletedCoefficient E δ hδ hδ0) := rfl

theorem cmFiniteTensorUnitary_original (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    (cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0 g))).val.val =
      g.val.val.map (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E) := by
  rw [cmFiniteTensorUnitary_matrix, Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix_rational,
    Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation_matrix]
  apply Matrix.ext
  intro i j
  exact (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational _ _ _).trans
    (congrArg (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E)
      ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).apply_symm_apply (g.val.val i j)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteTensorUnitary.Approximation
