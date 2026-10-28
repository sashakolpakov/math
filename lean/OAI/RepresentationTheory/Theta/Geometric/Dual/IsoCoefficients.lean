import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenRegularHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.IsoGaugeCompatibility
import OAI.RepresentationTheory.Theta.Geometric.Dual.SourceReduction

/-! # Iso Coefficients -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoefficients

noncomputable section

/-! Actual local coefficients of an infinitesimal theta-quotient
isomorphism, on their original projective coordinate opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {n m : ℕ}
    (f : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    (g : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))
    (t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X ⟶ X)

def dualThetaIsoFrameOpen (i : QuotientIndexedFrames.ThetaFrameIndex n m) : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left.Opens :=
  IsoFrameUnits.thetaIsoFrameOpen (t ≫ f).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
    (t ≫ g).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left (i, i)

def dualThetaIsoFrameUnit
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m) : Γ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⊗ X).left, dualThetaIsoFrameOpen f g t i)ˣ :=
  IsoFrameUnits.thetaIsoFrameUnitOn (t ≫ f).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
    (t ≫ g).left (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left e (i, i) _ le_rfl

def dualThetaIsoCoefficient
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : DualNumber ℂ :=
  OpenRegularValues.dualOpenRegularFunctionValue X (dualThetaIsoFrameOpen f g t i) (dualThetaIsoFrameUnit f g t e i) p

theorem dualThetaIsoCoefficient_isUnit
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hp : (BaseChangeReduction.dualBaseChangeReduction X).left (p.left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      dualThetaIsoFrameOpen f g t i) : IsUnit (dualThetaIsoCoefficient f g t e i p) := by
  unfold dualThetaIsoCoefficient
  rw [OpenRegularValues.dualOpenRegularFunctionValue_of_mem X _ _ p hp]
  exact (dualThetaIsoFrameUnit f g t e i).isUnit.map _

theorem dualThetaIsoCoefficient_differentiableAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [IsIntegral X.left] [Smooth X.hom]
    (e : (AlgebraicQuotient.algebraicThetaQuotient (t ≫ f).left (t ≫ g).left).sheaf ≅
      (AlgebraicQuotient.algebraicThetaQuotient (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ f).left
        (snd (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) X ≫ g).left).sheaf)
    (i : QuotientIndexedFrames.ThetaFrameIndex n m) (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (hz : (BaseChangeReduction.dualBaseChangeReduction X).left ((p z).left (default : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ∈
      dualThetaIsoFrameOpen f g t i) :
    CoefficientHolomorphic.DualCoefficientDifferentiableAt (dualThetaIsoCoefficient f g t e i ∘ p) z :=
  OpenRegularHolomorphic.dualOpenRegularFunctionValue_differentiableAt X _ _ p z hp hz

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.IsoCoefficients
