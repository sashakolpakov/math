import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ScalarRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Classifying Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ClassifyingBaseChange

noncomputable section

/-! The exact characteristic-zero PEL classifying property after extending
the coefficient number field. Both the new universal family and the
classifying maps are constructed by actual scheme pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K] [Field L] [NumberField L]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (j : K →+* L)

def characteristicZeroPELBaseChange {X : Over (Spec (.of K))}
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N X) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P (j.comp iota) N
      ((Over.pullback (Spec.map (CommRingCat.ofHom j))).obj X) :=
  Has.IntegralPELObject.toCharacteristicZero
    ((BaseChange.integralPELOfCharacteristicZero A).baseChange j)

def baseChangedFinePELModel (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) :
    AbelianModuli.ReferenceFamily.Models.FinePELModel P (j.comp iota) N where
  space := (Over.pullback (Spec.map (CommRingCat.ofHom j))).obj M.space
  universal := characteristicZeroPELBaseChange j M.universal

@[simp] theorem baseChangedFinePELModel_data (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) :
    Has.characteristicZeroPELData P (baseChangedFinePELModel j M).universal =
      (Has.characteristicZeroPELData P M.universal).pullback
        (pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom j))) := rfl

/-- The classifying predicate over L is precisely the original predicate
after restricting coefficients and applying the pullback adjunction. -/
theorem pel_baseChange_classifying_iff
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (Y : Over (Spec (.of L)))
    (A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P (j.comp iota) N Y)
    (f : Y ⟶ (baseChangedFinePELModel j M).space) :
    Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso (baseChangedFinePELModel j M).universal A f) ↔
      Nonempty (AbelianModuli.ReferenceFamily.Models.PELPullbackIso M.universal
        (ScalarRestriction.characteristicZeroPELRestrictScalars iota j Y A)
        (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom j))).homEquiv Y M.space).symm f)) := by
  let q := pullback.fst M.space.hom (Spec.map (CommRingCat.ofHom j))
  let U := Has.characteristicZeroPELData P M.universal
  constructor
  · rintro ⟨e⟩
    exact ⟨Iso.pelPullbackOfActionIso
      ((Iso.actionIsoOfPELPullback e).trans (Iso.PolarizedActionIso.pullbackComp U q f.left))⟩
  · rintro ⟨e⟩
    exact ⟨Iso.pelPullbackOfActionIso
      ((Iso.actionIsoOfPELPullback e).trans (Iso.PolarizedActionIso.pullbackComp U q f.left).symm)⟩

/-- The actual pulled-back universal family still classifies every PEL
object uniquely after extension of the coefficient number field. -/
theorem finePEL_isFine_baseChange (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    (baseChangedFinePELModel j M).IsFine := by
  intro Y A
  let e := (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom j))).homEquiv Y M.space
  obtain ⟨f, hf, huniq⟩ := hM (ScalarRestriction.coefficientRestriction j Y)
    (ScalarRestriction.characteristicZeroPELRestrictScalars iota j Y A)
  refine ⟨e f, ?_, ?_⟩
  · apply (pel_baseChange_classifying_iff j M Y A (e f)).mpr
    simpa only [e, Equiv.symm_apply_apply] using hf
  · intro g hg
    have h := huniq (e.symm g) ((pel_baseChange_classifying_iff j M Y A g).mp hg)
    exact e.symm.injective (h.trans (e.symm_apply_apply f).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ClassifyingBaseChange
