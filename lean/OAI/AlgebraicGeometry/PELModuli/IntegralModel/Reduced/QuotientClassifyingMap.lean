import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientLocalClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.PELFrameGeometry

/-! # Quotient Classifying Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Every prescribed integral PEL family on a reduced test scheme has
an actual map to the quotient. The map is constructed by classifying its
prime-level frame cover and descending along that finite etale cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s p N : ℕ} [NeZero p] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO p N X) (hU : U.IsFine)
    (π : X ⟶ Q)
    (hfib : U.ReducedQuotientFibers π)

include hU hfib in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.exists_reducedQuotient_classifying_map (hp : p.Prime) [IsReduced T.left]
    (A : PEL.Has.IntegralPELObject P R iotaO N T)
    (hunit : ∀ x : T.left, IsUnit (p : T.left.presheaf.stalk x)) :
    ∃ d : T ⟶ Q, ∃ f : IntegralPEL.FrameExistence.IntegralPELFrame.space A hunit ⟶ X,
      IntegralPEL.FrameExistence.IntegralPELFrame.forget A hunit ≫ d = f ≫ π ∧
      Nonempty (PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data
        (A.pullback (IntegralPEL.FrameExistence.IntegralPELFrame.forget A hunit)).data) := by
  let V := IntegralPEL.FrameExistence.IntegralPELFrame.space A hunit
  let q := IntegralPEL.FrameExistence.IntegralPELFrame.forget A hunit
  obtain ⟨hf, he, hs⟩ := IntegralPEL.PELFrameGeometry.IntegralPELFrame.finite_etale_surjective A hunit hp
  have : IsFinite q.left := hf
  have : Etale q.left := he
  have : Surjective q.left := hs
  have : IsReduced V.left := Finite.EtaleReduced.finite_etale_isReduced q.left
  obtain ⟨f, ⟨e⟩, _⟩ := hU V (IntegralPEL.FrameExistence.IntegralPELFrame.universal A hunit)
  have c : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data (A.pullback q).data :=
    e.forgetAuxiliary
  obtain ⟨d, hd, _⟩ := U.reducedQuotient_classifying_map π hfib A q f c
  exact ⟨d, f, hd, ⟨c⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
