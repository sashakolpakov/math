import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroTarget
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareFrame

/-! # Overlap Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual Poincare frame induces source and target frames along
the abelian zero section of the prescribed overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareSourceFrame :
    ((U.prescribedPoincareLine.pullback (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left).pullback
      (U.prescribedPoincareZeroOverlap π).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U.prescribedDualOverlap π).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left (U.prescribedPoincareZeroOverlap π).left
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_source π))

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTargetFrame (hrigid : U.PrescribedRigid) :
    ((U.prescribedPoincareLine.pullback (U.prescribedPoincareTarget π hU hk).left).pullback
      (U.prescribedPoincareZeroOverlap π).left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U.prescribedDualOverlap π).left :=
  LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
    (U.prescribedPoincareTarget π hU hk).left (U.prescribedPoincareZeroOverlap π).left
    (U.prescribedDualOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_target hU π hk hrigid))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
