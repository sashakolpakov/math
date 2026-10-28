import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.IsoInverse

/-! # Common Frame Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameProjection

noncomputable section

/-! The common-frame comparison constructs a finite etale surjective
map to the prescribed reference, with its actual universal-family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s L N : ℕ} [NeZero L] [NeZero N]
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X Y : Over (Spec (.of K))} [IsReduced X.left] [IsReduced Y.left]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

theorem common_frame_prescribed_projection
    (A : Has.IntegralPELObject P K iotaO N X) (B : Has.IntegralPELObject P K iotaO L Y)
    (hL : ∀ x : X.left, IsUnit (L : X.left.presheaf.stalk x))
    (hN : ∀ y : Y.left, IsUnit (N : Y.left.presheaf.stalk y))
    (hN3 : 3 ≤ N) (hL3 : 3 ≤ L) (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (hA : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (C : Has.IntegralPELObject P K iotaO N T),
      ∃! f : T ⟶ X, Nonempty (Iso.PolarizedActionIso (A.pullback f).data C.data))
    (hB : ∀ (T : Over (Spec (.of K))) [IsReduced T.left]
      (C : Has.IntegralPELObject P K iotaO L T),
      ∃! f : T ⟶ Y, Nonempty (Iso.PolarizedActionIso (B.pullback f).data C.data)) :
    ∃ q : IntegralPEL.FrameExistence.IntegralPELFrame.space B hN ⟶ X, IsFinite q.left ∧ Etale q.left ∧ Surjective q.left ∧
      Nonempty (Iso.PolarizedActionIso (A.pullback q).data (IntegralPEL.FrameExistence.IntegralPELFrame.universal B hN).swap.forgetAuxiliary.data) := by
  obtain ⟨e, ⟨he⟩⟩ := CommonFrameComparison.pel_common_frame_comparison A B hL hN hN3 hL3 hPresentations hA hB
  let a := IntegralAdded.PELId.IntegralAddedPELLevel.comparisonOverInverse (IntegralPEL.FrameExistence.IntegralPELFrame.universal A hL) (IntegralPEL.FrameExistence.IntegralPELFrame.universal B hN).swap e he
  let f := IntegralPEL.FrameExistence.IntegralPELFrame.forget A hL
  let q := e.inv ≫ f
  obtain ⟨hf, ht, hs⟩ := IntegralPEL.FrameCharacteristicZero.IntegralPELFrame.characteristicZero_finite_etale_surjective A hL
  have : IsFinite f.left := hf
  have : Etale f.left := ht
  have : Surjective f.left := hs
  have : IsIso e.inv.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_inv
  refine ⟨q, inferInstanceAs (IsFinite (e.inv.left ≫ f.left)),
    inferInstanceAs (Etale (e.inv.left ≫ f.left)), inferInstanceAs (Surjective (e.inv.left ≫ f.left)), ?_⟩
  exact ⟨(Iso.PolarizedActionIso.pullbackComp A.data f.left e.inv.left).symm.trans a.forgetAuxiliary⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.CommonFrameProjection
