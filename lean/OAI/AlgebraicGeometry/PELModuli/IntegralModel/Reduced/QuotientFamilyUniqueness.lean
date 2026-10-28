import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.QuotientLocalClassification

/-! # Quotient Family Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Maps to the actual prescribed quotient are determined by their
pulled-back PEL family. Lift both maps to a common finite etale cover
and use the original prescribed-family kernel-pair characterization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q T : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] [Surjective π.left]
    (hfib : U.ReducedQuotientFibers π)
    (A : PEL.Has.PolarizedActionData E (3 * s) P.polarizationType N Q.left)
    (e : PEL.Iso.PolarizedActionIso U.forgetAuxiliary.data (A.pullback π.left))

include hfib e in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.reducedQuotient_family_determines_map [IsReduced T.left] (g d : T ⟶ Q)
    (h : PEL.Iso.PolarizedActionIso (A.pullback g.left) (A.pullback d.left)) : g = d := by
  let V := Limits.pullback g π
  let v := pullback.fst g π
  let a := pullback.snd g π
  let W := Limits.pullback (v ≫ d) π
  let w := pullback.fst (v ≫ d) π
  let b := pullback.snd (v ≫ d) π
  have hv := (IsPullback.of_hasPullback g π).map (Over.forget (Spec (.of R)))
  have hw := (IsPullback.of_hasPullback (v ≫ d) π).map (Over.forget (Spec (.of R)))
  have : IsFinite v.left := MorphismProperty.of_isPullback hv.flip (inferInstanceAs (IsFinite π.left))
  have : Etale v.left := MorphismProperty.of_isPullback hv.flip (inferInstanceAs (Etale π.left))
  have : Surjective v.left := MorphismProperty.of_isPullback hv.flip (inferInstanceAs (Surjective π.left))
  have : IsFinite w.left := MorphismProperty.of_isPullback hw.flip (inferInstanceAs (IsFinite π.left))
  have : Etale w.left := MorphismProperty.of_isPullback hw.flip (inferInstanceAs (Etale π.left))
  have : Surjective w.left := MorphismProperty.of_isPullback hw.flip (inferInstanceAs (Surjective π.left))
  have : IsReduced V.left := Finite.EtaleReduced.finite_etale_isReduced v.left
  have : IsReduced W.left := Finite.EtaleReduced.finite_etale_isReduced w.left
  let q := w ≫ v
  let f₁ := w ≫ a
  let f₂ := b
  have h₁ : f₁ ≫ π = q ≫ g := by
    change (w ≫ a) ≫ π = (w ≫ v) ≫ g
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have h₂ : f₂ ≫ π = q ≫ d := by
    exact pullback.condition.symm.trans (Category.assoc w v d).symm
  let c₁ : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f₁).data
      ((A.pullback g.left).pullback q.left) :=
    (e.pullback f₁.left).trans ((PEL.Iso.PolarizedActionIso.pullbackComp A π.left f₁.left).trans
      ((PEL.Iso.PolarizedActionIso.pullbackCongr A _ _ (congrArg Over.Hom.left h₁)).trans
        (PEL.Iso.PolarizedActionIso.pullbackComp A g.left q.left).symm))
  let c₂ : PEL.Iso.PolarizedActionIso (U.forgetAuxiliary.pullback f₂).data
      ((A.pullback d.left).pullback q.left) :=
    (e.pullback f₂.left).trans ((PEL.Iso.PolarizedActionIso.pullbackComp A π.left f₂.left).trans
      ((PEL.Iso.PolarizedActionIso.pullbackCongr A _ _ (congrArg Over.Hom.left h₂)).trans
        (PEL.Iso.PolarizedActionIso.pullbackComp A d.left q.left).symm))
  have he : f₁ ≫ π = f₂ ≫ π :=
    (hfib W f₁ f₂).mpr
      ⟨c₁.trans ((h.pullback q.left).trans c₂.symm)⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi (w.left ≫ v.left)).mp
  exact congrArg Over.Hom.left (h₁.symm.trans (he.trans h₂))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
