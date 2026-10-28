import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLocalLevel
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelFromLocalSections

/-! # Pair Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual arithmetic abelian quotient carries the prescribed full
ordered level. Its labelled sections and complete functor pullback recover
the original marking under the constructed native family comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b) (hrigid : U.PrescribedRigid)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.fullLevel : B.abelian.FullLevel N := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact LevelFromLocalSections.fullLevelOfLocalSections ((Over.pullback b).map π).left B.abelian B.localLevel
    (B.levelSection hrigid) (B.levelSection_pullback hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.fullLevel_section (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    LevelSections.fullLevelSection (B.fullLevel hrigid) c = B.levelSection hrigid c := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact LevelFromLocalSections.fullLevelOfLocalSections_section ((Over.pullback b).map π).left B.abelian B.localLevel
    (B.levelSection hrigid) (B.levelSection_pullback hrigid) c

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.fullLevel_pullback : (B.fullLevel hrigid).pullback ((Over.pullback b).map π).left =
    B.localLevel := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  exact LevelFromLocalSections.fullLevelOfLocalSections_pullback ((Over.pullback b).map π).left B.abelian B.localLevel
    (B.levelSection hrigid) (B.levelSection_pullback hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
