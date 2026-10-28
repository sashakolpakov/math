import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteTensorUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryHomeomorph
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecialUnitaryBaseChange
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryLinear

/-! # Finite PEL Homeomorph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph.Approximation

noncomputable section

/-! Identify the actual CM restricted unitary group with the original
PEL finite group, as topological groups and on every rational matrix. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

def cmFiniteTensorHomeomorph :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) ≃ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E b)) :=
  (Finite.UnitaryHomeomorph.Approximation.finiteUnitaryCompletedHomeomorph (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)).trans
    ((SpecialUnitaryBaseChange.Approximation.specialUnitaryScalarHomeomorph
      (QuadraticTensorEquiv.TestTransport.quadraticAdelicTensorRingEquiv (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0))
      (FiniteTensorUnitary.Approximation.cmCompletedCoefficient_star E δ hδ hδ0) _
      (QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous _ _) (QuadraticTensorEquiv.TestTransport.quadraticTensorInverse_continuous _ _)).trans
        { toMulEquiv := UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (FiniteTensorUnitary.Approximation.cmCompletedHermitianMatrix E δ hδ hδ0 b hb hb0)
          continuous_toFun := Quaternion.LocalUnitary.unitaryFormCongr_continuous _ _
            (FiniteTensorUnitary.Approximation.cmCompletedHermitianMatrix E δ hδ hδ0 b hb hb0)
          continuous_invFun := Quaternion.LocalUnitary.unitaryFormCongr_continuous _ _
            (FiniteTensorUnitary.Approximation.cmCompletedHermitianMatrix E δ hδ hδ0 b hb hb0).symm })

theorem cmFiniteTensorHomeomorph_apply
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)) :
    cmFiniteTensorHomeomorph E δ hδ hδ0 b hb hb0 g =
      FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary E δ hδ hδ0 b hb hb0 g := rfl

variable {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def cmFinitePELHomeomorph
    (hP : IsCMField.complexConj E P.b = P.b) (hP0 : P.b ≠ 0) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hP hP0) ≃ₜ*
      P.FiniteSpecialUnitary :=
  (cmFiniteTensorHomeomorph E δ hδ hδ0 P.b hP hP0).trans (UnitaryLinear.Approximation.matrixPELUnitaryHomeomorph E P)

theorem cmFinitePELHomeomorph_original
    (hP : IsCMField.complexConj E P.b = P.b) (hP0 : P.b ≠ 0)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (i j : Fin 3) :
    (cmFinitePELHomeomorph E δ hδ hδ0 P hP hP0
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ P.b hP hP0)
        (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 P.b hP hP0 g))).val (Pi.single j 1) i =
      AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (g.val.val i j) :=
  (UnitaryLinear.Approximation.matrixPELUnitary_entry E P _ i j).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => M i j)
      (FiniteTensorUnitary.Approximation.cmFiniteTensorUnitary_original E δ hδ hδ0 P.b hP hP0 g))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FinitePELHomeomorph.Approximation
