import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.NormalizedIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.NormalizedRestriction

/-! # Normalized Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Restriction of the constructed Poincare isomorphism preserves the
frames specified by the actual dual source and target projections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_restrict {Y B : Over (Spec (.of R))}
    (r : Y ⟶ U.prescribedPoincareOverlap π) (w : B ⟶ Y) (b : B ⟶ U.prescribedDualOverlap π)
    (hw : w ≫ r = b ≫ U.prescribedPoincareZeroOverlap π)
    (f g : Y ⟶ U.prescribedPoincareSpace) (a c : B ⟶ U.prescribedDualTotalSpace)
    (hf : r ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection = f)
    (hg : r ≫ U.prescribedPoincareTarget π hU hk = g)
    (ha : b ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection = a)
    (hc : b ≫ U.prescribedDualOverlapTarget hU π hk = c)
    (h : w ≫ f = a ≫ U.prescribedPoincareZero) (k : w ≫ g = c ≫ U.prescribedPoincareZero) :
    (Scheme.Modules.pullback w.left).mapIso
      (LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine
        (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
        (U.prescribedPoincareTarget π hU hk).left r.left f.left g.left
        (congrArg Over.Hom.left hf) (congrArg Over.Hom.left hg)
        (U.prescribedPoincareNormalizedIso hU π hk hrigid)) ≪≫
      LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
        g.left w.left c.left (congrArg Over.Hom.left k) =
      LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left U.prescribedPoincareFrame
        f.left w.left a.left (congrArg Over.Hom.left h) := by
  exact LineBundle.NormalizedRestriction.lineBundleRestrictIso_normalized U.prescribedPoincareLine
    U.prescribedPoincareZero.left U.prescribedPoincareFrame
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
    (U.prescribedPoincareTarget π hU hk).left (U.prescribedPoincareZeroOverlap π).left
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left (U.prescribedDualOverlapTarget hU π hk).left
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_source π))
    (congrArg Over.Hom.left (U.prescribedPoincareZeroOverlap_target hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)
    (Iso.ext (U.prescribedPoincareNormalizedIso_normalized hU π hk hrigid))
    r.left w.left b.left (congrArg Over.Hom.left hw) f.left g.left a.left c.left
    (congrArg Over.Hom.left hf) (congrArg Over.Hom.left hg)
    (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hc)
    (congrArg Over.Hom.left h) (congrArg Over.Hom.left k)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
