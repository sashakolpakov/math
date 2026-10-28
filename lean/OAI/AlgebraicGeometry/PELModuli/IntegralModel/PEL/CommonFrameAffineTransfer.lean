import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameProjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleCoverBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.QuotientBaseChangeAffine

/-! # Common Frame Affine Transfer -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameAffineTransfer

noncomputable section

/-! A fine reference inherits affine neighborhoods from another
fine reference through their actual common level cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry.IntegralPELFrame
variable {E K K' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] [Field K'] {s L N : ℕ} [NeZero L] [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X Y : Over (Spec (.of K))} [IsReduced X.left] [IsReduced Y.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

theorem common_frame_affine_transfer
    (A : Has.IntegralPELObject P K iotaO N X) (B : Has.IntegralPELObject P K iotaO L Y)
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))
    (hN : ∀ y : Y.left, IsUnit (N : Y.left.presheaf.stalk y))
    (hN3 : 3 ≤ N) (hL3 : 3 ≤ L) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hA : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (C : Has.IntegralPELObject P K iotaO N T),
      ∃! f : T ⟶ X, Nonempty (Iso.PolarizedActionIso (A.pullback f).data C.data))
    (hB : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (C : Has.IntegralPELObject P K iotaO L T),
      ∃! f : T ⟶ Y, Nonempty (Iso.PolarizedActionIso (B.pullback f).data C.data))
    (φ : K →+* K')
    (hA' : ∀ (T : Over (Spec (.of K'))) [IsReduced T.left]
      (C : Has.IntegralPELObject P K' (φ.comp iotaO) N T),
      ∃! f : T ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X,
        Nonempty (Iso.PolarizedActionIso ((A.baseChange φ).pullback f).data C.data))
    (hred : IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left)
    (hsep : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.IsSeparated)
    (hAF : ∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj Y).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) :
    IsReduced ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left ∧
    (∀ F : Set ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left,
      F.Finite → ∃ V : ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X).left.Opens,
        IsAffineOpen V ∧ F ⊆ V) := by
  let W := IntegralPEL.FrameExistence.IntegralPELFrame.space B hN
  let U := (IntegralPEL.FrameExistence.IntegralPELFrame.universal B hN).swap
  let f := IntegralPEL.FrameExistence.IntegralPELFrame.forget B hN
  obtain ⟨hf, ht, _⟩ := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_finite_etale_surjective B hN
  have : IsFinite f.left := hf
  have : Etale f.left := ht
  obtain ⟨hwred, hwn⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.reduced_noetherian B hN
  have : IsReduced W.left := hwred
  have : IsNoetherian W.left := hwn
  have : LocallyOfFiniteType W.hom := by
    rw [← f.w]
    infer_instance
  have hu : U.IsFine := IntegralAdded.FineSwap.integralAddedPEL_fine_swap (IntegralPEL.FrameExistence.IntegralPELFrame.universal B hN) (IntegralPEL.FrameFine.IntegralPELFrame.isFine B hN hL3 hPresentations hB)
  obtain ⟨q, hqf, hqt, hqs, ⟨e⟩⟩ :=
    CommonFrameProjection.common_frame_prescribed_projection A B hL hN hN3 hL3 hPresentations hA hB
  have : IsFinite q.left := hqf
  have : Etale q.left := hqt
  have : Surjective q.left := hqs
  obtain ⟨hredW, hsepW, hAFW⟩ := IntegralModel.Finite.EtaleCoverBaseChange.finite_etale_cover_baseChange_geometry φ f hred hsep hAF
  exact QuotientBaseChangeAffine.auxiliary_quotient_baseChange_affine U hu A q e hN3 hPresentations φ hA' hredW hsepW hAFW

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameAffineTransfer
