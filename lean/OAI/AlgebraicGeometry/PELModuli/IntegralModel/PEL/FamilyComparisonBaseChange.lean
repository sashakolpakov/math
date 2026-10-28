import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.RelativePullback

/-! # Family Comparison Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.FamilyComparisonBaseChange

noncomputable section

/-! The actual polarized family comparison commutes with coefficient
extension and the induced map of the parameter schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y : Over (Spec (.of R))}

def prescribedFamilyComparisonBaseChange
    (A : Has.IntegralPELObject P R iotaO N Y) (B : Has.IntegralPELObject P R iotaO N X)
    (q : X ⟶ Y) (e : Iso.PolarizedActionIso (A.pullback q).data B.data) (φ : R →+* R') :
    Iso.PolarizedActionIso
      ((A.baseChange φ).pullback ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).map q)).data
      (B.baseChange φ).data := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let x := pullback.fst X.hom b
  let y := pullback.fst Y.hom b
  let q' := ((Over.pullback b).map q).left
  have h : q' ≫ y = x ≫ q.left := by
    dsimp [q', x, y]
    exact pullback.lift_fst _ _ _
  exact (Iso.PolarizedActionIso.pullbackComp A.data y q').trans
    ((Iso.PolarizedActionIso.pullbackCongr A.data _ _ h).trans
      ((Iso.PolarizedActionIso.pullbackComp A.data q.left x).symm.trans (e.pullback x)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.FamilyComparisonBaseChange
