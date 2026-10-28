import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.PolarizationOverlap

/-! # Scalar Polarization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original actual polarization and all its scalar changes are
finite, flat, and surjective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) {S : Scheme.{0}} (b : S ⟶ Spec (.of R))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarization_finite : IsFinite U.prescribedPolarization.left :=
  inferInstanceAs (IsFinite U.forgetAuxiliary.data.polarized.polarization.isogeny.hom.left)

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarization_flat : Flat U.prescribedPolarization.left :=
  inferInstanceAs (Flat U.forgetAuxiliary.data.polarized.polarization.isogeny.hom.left)

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarization_surjective : Surjective U.prescribedPolarization.left :=
  inferInstanceAs (Surjective U.forgetAuxiliary.data.polarized.polarization.isogeny.hom.left)

instance IntegralAdded.PELId.IntegralAddedPELLevel.scalarPolarization_finite : IsFinite ((Over.pullback b).map U.prescribedPolarization).left :=
  MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedPolarization)
    (inferInstanceAs (IsFinite U.prescribedPolarization.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.scalarPolarization_flat : Flat ((Over.pullback b).map U.prescribedPolarization).left :=
  MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedPolarization)
    (inferInstanceAs (Flat U.prescribedPolarization.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.scalarPolarization_surjective : Surjective ((Over.pullback b).map U.prescribedPolarization).left :=
  MorphismProperty.of_isPullback (Specialization.base_change_square b U.prescribedPolarization)
    (inferInstanceAs (Surjective U.prescribedPolarization.left))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
