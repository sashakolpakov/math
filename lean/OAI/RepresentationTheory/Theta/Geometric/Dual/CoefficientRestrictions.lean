import OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoefficients
import OAI.RepresentationTheory.Theta.Geometric.Dual.UnitEvaluation

/-! # Coefficient Restrictions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientRestrictions

noncomputable section

/-! The actual infinitesimal isomorphism coefficient may be evaluated
on any smaller common open without changing its value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem dualThetaIsoCoefficient_value_on {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n m : ℕ}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (W : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hW : W ≤ IsoCoefficients.dualThetaIsoFrameOpen f g t i)
    (hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈ W) :
    IsoCoefficients.dualThetaIsoCoefficient f g t e i p =
      OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left W (OpenRegularValues.dualConstantPoint_open_range X p W hp)
        (IsoFrameUnits.thetaIsoFrameUnitOn (t ≫ f).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
          (t ≫ g).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left e (i, i) W hW :
            Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, W)) := by
  have H := IsoFrameUnits.thetaIsoFrameUnitOn_restrict (t ≫ f).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
    (t ≫ g).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left e (i, i) hW le_rfl
  have HV := congrArg (fun u : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, W)ˣ =>
    OpenSectionValues.dualSectionValue (AffineBaseChangeChart.dualConstantPoint X p).left W (OpenRegularValues.dualConstantPoint_open_range X p W hp)
      (u : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, W))) H
  have hr := UnitEvaluation.restrictRegularUnit_dualValue hW (IsoCoefficients.dualThetaIsoFrameUnit f g t e i)
    (AffineBaseChangeChart.dualConstantPoint X p).left (OpenRegularValues.dualConstantPoint_open_range X p W hp)
  exact (OpenRegularValues.dualOpenRegularFunctionValue_of_mem X _ _ p (hW hp)).trans (hr.symm.trans HV)

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientRestrictions
