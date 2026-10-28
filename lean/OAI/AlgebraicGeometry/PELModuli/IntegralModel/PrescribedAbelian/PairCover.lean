import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.Pair

/-! # Pair Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The prescribed cartesian family covers are finite etale and
surjective; the actual quotient families are locally noetherian. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianCover_finite : IsFinite B.abelianCover :=
  MorphismProperty.of_isPullback B.abelianCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (IsFinite π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualCover_finite : IsFinite B.dualCover :=
  MorphismProperty.of_isPullback B.dualCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (IsFinite π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianCover_etale : Etale B.abelianCover :=
  MorphismProperty.of_isPullback B.abelianCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualCover_etale : Etale B.dualCover :=
  MorphismProperty.of_isPullback B.dualCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianCover_surjective [Surjective π.left] : Surjective B.abelianCover :=
  MorphismProperty.of_isPullback B.abelianCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualCover_surjective [Surjective π.left] : Surjective B.dualCover :=
  MorphismProperty.of_isPullback B.dualCartesian
    (MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left)))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelian_locallyNoetherian [IsLocallyNoetherian ((Over.pullback b).obj Q).left] :
    IsLocallyNoetherian B.abelian.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian B.abelian.scheme.hom

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dual_locallyNoetherian [IsLocallyNoetherian ((Over.pullback b).obj Q).left] :
    IsLocallyNoetherian B.dual.scheme.left :=
  LocallyOfFiniteType.isLocallyNoetherian B.dual.scheme.hom

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
