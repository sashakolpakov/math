import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CharacteristicZeroFamilyRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FrameRigidity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineComparison

/-! # Reference Frame Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ReferenceFrameComparison

noncomputable section

/-! A bounded fine two-level PEL model is the actual prime-frame cover
of any given reduced fine prescribed-level PEL model. The latter needs
no geometric finiteness hypothesis for this universal-family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s p N : ℕ} [Fact p.Prime]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}

theorem pel_reference_frame_comparison
    (V : Over (Spec (.of K))) [IsReduced V.left] [IsNoetherian V.left] [LocallyOfFiniteType V.hom]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO p N V) (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hU : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (A : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO p N T),
      ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (X : Over (Spec (.of K))) [IsReduced X.left] (A : Has.IntegralPELObject P K iotaO N X)
    (hA : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (B : Has.IntegralPELObject P K iotaO N T),
      ∃! f : T ⟶ X, Nonempty (Iso.PolarizedActionIso (A.pullback f).data B.data))
    (hp : ∀ x : X.left, IsUnit (p : X.left.presheaf.stalk x)) :
    ∃ e : V ≅ IntegralPEL.FrameExistence.IntegralPELFrame.space A hp,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((IntegralPEL.FrameExistence.IntegralPELFrame.universal A hp).pullback e.hom) U) := by
  have hRigid := CharacteristicZeroFamilyRigidity.characteristicZero_pel_family_rigidity U hN hPresentations
    (fun T _ B => (hU T B).exists)
  have : IsFinite (IntegralPEL.FrameExistence.IntegralPELFrame.forget A hp).left :=
    Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_isFinite (IntegralPEL.FrameExistence.IntegralPELFrame.pureModel A) hp
  have : Etale (IntegralPEL.FrameExistence.IntegralPELFrame.forget A hp).left :=
    Integral.PureAddedLevel.IntegralPureModel.addedLevelForget_etale (IntegralPEL.FrameExistence.IntegralPELFrame.pureModel A) hp
  have : IsReduced (IntegralPEL.FrameExistence.IntegralPELFrame.space A hp).left :=
    Finite.EtaleReduced.finite_etale_isReduced (IntegralPEL.FrameExistence.IntegralPELFrame.forget A hp).left
  exact IntegralAdded.FineComparison.integralAddedPEL_fine_comparison V (IntegralPEL.FrameExistence.IntegralPELFrame.space A hp) U
    (IntegralPEL.FrameExistence.IntegralPELFrame.universal A hp) hU
    (IntegralPEL.FrameRigidity.IntegralPELFrame.isFine_of_family_rigidity A hp hA hRigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ReferenceFrameComparison
