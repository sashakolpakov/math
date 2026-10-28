import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PrimeLevelCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # PEL Frame Geometry -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry.IntegralPELFrame

noncomputable section

/-! The actual prime-frame cover is finite etale and surjective; over
a reduced noetherian base it remains reduced and noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s p N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : PEL.Has.IntegralPELObject P R iotaO N X) [NeZero p]
    (hp : ∀ x : X.left, IsUnit (p : X.left.presheaf.stalk x))

theorem finite_etale_surjective (hprime : p.Prime) :
    IsFinite (FrameExistence.IntegralPELFrame.forget U hp).left ∧ Etale (FrameExistence.IntegralPELFrame.forget U hp).left ∧ Surjective (FrameExistence.IntegralPELFrame.forget U hp).left := by
  have : Fact p.Prime := ⟨hprime⟩
  exact ⟨Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_isFinite (FrameExistence.IntegralPELFrame.pureModel U) hp,
    Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_etale (FrameExistence.IntegralPELFrame.pureModel U) hp,
    Integral.PrimeLevelCover.IntegralLevelCover.prime_fullFrame_surjective U.data.polarized.abelian hp⟩

theorem reduced_noetherian [IsReduced X.left] [IsNoetherian X.left] :
    IsReduced (FrameExistence.IntegralPELFrame.space U hp).left ∧ IsNoetherian (FrameExistence.IntegralPELFrame.space U hp).left := by
  have : IsFinite (FrameExistence.IntegralPELFrame.forget U hp).left := Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_isFinite (FrameExistence.IntegralPELFrame.pureModel U) hp
  have : Etale (FrameExistence.IntegralPELFrame.forget U hp).left := Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_etale (FrameExistence.IntegralPELFrame.pureModel U) hp
  have : IsLocallyNoetherian (FrameExistence.IntegralPELFrame.space U hp).left :=
    LocallyOfFiniteType.isLocallyNoetherian (FrameExistence.IntegralPELFrame.forget U hp).left
  have : CompactSpace (FrameExistence.IntegralPELFrame.space U hp).left := QuasiCompact.compactSpace_of_compactSpace (FrameExistence.IntegralPELFrame.forget U hp).left
  exact ⟨AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource (FrameExistence.IntegralPELFrame.forget U hp).left, ⟨⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry.IntegralPELFrame
