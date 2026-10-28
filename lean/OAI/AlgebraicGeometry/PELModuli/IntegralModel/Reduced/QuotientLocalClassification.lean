import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientFiberCondition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverKernelPairFactor

/-! # Quotient Local Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A classifying map on an actual finite etale cover descends to the
prescribed quotient when the local prescribed family is the pullback of
the given family. Every base test used for classification is reduced, while the parameter
cover itself may be a nonreduced scalar change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T V W : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (π : X ⟶ Q)
    (hfib : U.ReducedQuotientFibers π)
    (A : PEL.Has.IntegralPELObject P R iotaO N T) (q : V ⟶ T) (f : V ⟶ X)
    (e : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f).data (A.pullback q).data)

include hfib e in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotient_classifying_overlap [IsReduced W.left] (a b : W ⟶ V)
    (hab : a ≫ q = b ≫ q) : (a ≫ f) ≫ π = (b ≫ f) ≫ π := by
  let c (k : W ⟶ V) : PEL.Iso.PolarizedActionIso
      (U.forgetAuxiliary.pullback (k ≫ f)).data (A.pullback (k ≫ q)).data :=
    (PEL.Iso.PolarizedActionIso.pullbackComp U.forgetAuxiliary.data f.left k.left).symm.trans
      ((e.pullback k.left).trans (PEL.Iso.PolarizedActionIso.pullbackComp A.data q.left k.left))
  apply (hfib W (a ≫ f) (b ≫ f)).mpr
  exact ⟨(c a).trans ((PEL.Iso.PolarizedActionIso.pullbackCongr A.data _ _
    (congrArg Over.Hom.left hab)).trans (c b).symm)⟩

include hfib e in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotient_classifying_map [IsReduced T.left]
    [IsFinite q.left] [Etale q.left] [Surjective q.left] :
    ∃! d : T ⟶ Q, q ≫ d = f ≫ π := by
  have : IsReduced V.left := Finite.EtaleReduced.finite_etale_isReduced q.left
  have hq := (IsPullback.of_hasPullback q q).map (Over.forget (Spec (.of R)))
  have : IsFinite (pullback.fst q q).left := MorphismProperty.of_isPullback hq.flip
    (inferInstanceAs (IsFinite q.left))
  have : Etale (pullback.fst q q).left := MorphismProperty.of_isPullback hq.flip
    (inferInstanceAs (Etale q.left))
  have : IsReduced (Limits.pullback q q).left := Finite.EtaleReduced.finite_etale_isReduced (pullback.fst q q).left
  apply OverKernelPairFactor.over_factor_of_kernelPair q (pullback.fst q q).left (pullback.snd q q).left hq (f ≫ π)
  have h := congrArg Over.Hom.left
    (U.reducedQuotient_classifying_overlap π hfib A q f e (pullback.fst q q) (pullback.snd q q) pullback.condition)
  simpa only [Over.comp_left, Category.assoc] using h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
