import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.Classification

/-! # Iso Inverse -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded

noncomputable section

/-! Invert a universal-family comparison along an actual parameter
scheme isomorphism, retaining both ordered markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y : Over (Spec (.of R))}

def PELId.IntegralAddedPELLevel.comparisonOverInverse (A : PELId.IntegralAddedPELLevel P R iotaO L N X)
    (B : PELId.IntegralAddedPELLevel P R iotaO L N Y) (e : X ≅ Y)
    (h : PELId.IntegralAddedPELLevel.Iso (B.pullback e.hom) A) : PELId.IntegralAddedPELLevel.Iso (A.pullback e.inv) B :=
  (h.pullback e.inv).symm.trans
    ((B.pullbackCompIso e.hom e.inv).trans
      ((B.pullbackCongrIso _ _ e.inv_hom_id).trans B.pullbackIdIso))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded
