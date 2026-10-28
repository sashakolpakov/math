import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.ScalarRestriction

/-! # Scalar Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

/-! Both-level integral PEL data commute with change and restriction of
the coefficient ring. The geometric Lie condition is the proved scalar
restriction condition for the same actual action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.baseChange (A : PELId.IntegralAddedPELLevel P R iotaO L N X)
    (φ : R →+* R') : PELId.IntegralAddedPELLevel P R' (φ.comp iotaO) L N
      ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) where
  auxiliary := A.auxiliary.baseChange φ
  prescribed := A.prescribed.pullback (pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ)))

def PELId.IntegralAddedPELLevel.restrictScalars (φ : R →+* R') (Y : Over (Spec (.of R')))
    (A : PELId.IntegralAddedPELLevel P R' (φ.comp iotaO) L N Y) :
    PELId.IntegralAddedPELLevel P R iotaO L N (PEL.ScalarRestriction.coefficientRestriction φ Y) where
  auxiliary := A.auxiliary.restrictScalars φ Y
  prescribed := A.prescribed

theorem ScalarChange.integralAddedPEL_baseChange_classifying_iff (φ : R →+* R')
    (U : PELId.IntegralAddedPELLevel P R iotaO L N X) (Y : Over (Spec (.of R')))
    (A : PELId.IntegralAddedPELLevel P R' (φ.comp iotaO) L N Y)
    (f : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj X) :
    Nonempty (PELId.IntegralAddedPELLevel.Iso ((U.baseChange φ).pullback f) A) ↔
      Nonempty (PELId.IntegralAddedPELLevel.Iso
        (U.pullback (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom φ))).homEquiv Y X).symm f))
        (A.restrictScalars φ Y)) := by
  let q := pullback.fst X.hom (Spec.map (CommRingCat.ofHom φ))
  constructor
  · rintro ⟨e⟩
    exact ⟨{
      auxiliary := (PEL.Iso.PolarizedActionIso.pullbackComp U.auxiliary.data q f.left).symm.trans e.auxiliary
      prescribed := ((AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackCompIso U.pure q f.left).symm.trans e.toPure).prescribed }⟩
  · rintro ⟨e⟩
    exact ⟨{
      auxiliary := (PEL.Iso.PolarizedActionIso.pullbackComp U.auxiliary.data q f.left).trans e.auxiliary
      prescribed := ((AbelianModuli.ReferenceFamily.Level.Data.AddedFullLevel.pullbackCompIso U.pure q f.left).trans e.toPure).prescribed }⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
