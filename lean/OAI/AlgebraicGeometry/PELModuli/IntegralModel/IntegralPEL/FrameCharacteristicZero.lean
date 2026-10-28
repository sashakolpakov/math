import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameExistence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CharacteristicZeroLevelCover
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced

/-! # Frame Characteristic Zero -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameCharacteristicZero.IntegralPELFrame

noncomputable section

/-! Actual finite etale covers at arbitrary levels of characteristic-zero
integral PEL families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] {s L N : ℕ} [NeZero L]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X : Over (Spec (.of K))} (U : PEL.Has.IntegralPELObject P K iotaO N X)
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))

theorem characteristicZero_finite_etale_surjective :
    IsFinite (FrameExistence.IntegralPELFrame.forget U hL).left ∧ Etale (FrameExistence.IntegralPELFrame.forget U hL).left ∧ Surjective (FrameExistence.IntegralPELFrame.forget U hL).left :=
  ⟨Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_isFinite (FrameExistence.IntegralPELFrame.pureModel U) hL,
    Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_etale (FrameExistence.IntegralPELFrame.pureModel U) hL,
    Integral.CharacteristicZeroLevelCover.IntegralLevelCover.characteristicZero_fullFrame_surjective U.data.polarized X.hom hL⟩

theorem characteristicZero_reduced [IsReduced X.left] : IsReduced (FrameExistence.IntegralPELFrame.space U hL).left := by
  obtain ⟨hf, he, _⟩ := characteristicZero_finite_etale_surjective U hL
  have : IsFinite (FrameExistence.IntegralPELFrame.forget U hL).left := hf
  have : Etale (FrameExistence.IntegralPELFrame.forget U hL).left := he
  exact Finite.EtaleReduced.finite_etale_isReduced (FrameExistence.IntegralPELFrame.forget U hL).left

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameCharacteristicZero.IntegralPELFrame
