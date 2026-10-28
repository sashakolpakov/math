import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPEL.FamilyFibers

/-! # Fine Map Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineMapFibers

noncomputable section

/-! A map comparing an actual PEL family to a fine universal family
has precisely the prescribed family-isomorphism fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Y T : Over (Spec (.of R))}

theorem finePEL_map_eq_iff_prescribed_iso
    (A : PEL.Has.IntegralPELObject P R iotaO N Y) (U : PEL.Has.IntegralPELObject P R iotaO N X)
    (hA : ∀ (T : Over (Spec (.of R))) [IsReduced T.left]
      (B : PEL.Has.IntegralPELObject P R iotaO N T),
      ∃! f : T ⟶ Y, Nonempty (PEL.Iso.PolarizedActionIso (A.pullback f).data B.data))
    (q : X ⟶ Y) (e : PEL.Iso.PolarizedActionIso (A.pullback q).data U.data)
    [IsReduced T.left] (f g : T ⟶ X) :
    f ≫ q = g ≫ q ↔ Nonempty (PEL.Iso.PolarizedActionIso (U.pullback f).data (U.pullback g).data) := by
  constructor
  · intro h
    exact ⟨IntegralPEL.FamilyFibers.prescribedFamilyFiberComparison A U q e f g h⟩
  · rintro ⟨a⟩
    obtain ⟨k, _, hk⟩ := hA T (U.pullback g)
    exact (hk (f ≫ q) ⟨(IntegralPEL.FamilyFibers.prescribedFamilyPullbackComparison A U q e f).trans a⟩).trans
      (hk (g ≫ q) ⟨IntegralPEL.FamilyFibers.prescribedFamilyPullbackComparison A U q e g⟩).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FineMapFibers
