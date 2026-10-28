import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationCartesian
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ScalarPolarization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.FiniteCoverDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.MorphismDescent

/-! # Pair Polarization Isogeny -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual descended polarization morphism is a finite flat
surjective group morphism, constructed as an isogeny on the quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

variable (hrigid : U.PrescribedRigid)

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_proper : IsProper (B.polarizationMap hrigid).left := by
  have : IsProper ((B.polarizationMap hrigid).left ≫ B.dual.scheme.hom) := by
    rw [(B.polarizationMap hrigid).w]
    infer_instance
  exact IsProper.of_comp (B.polarizationMap hrigid).left B.dual.scheme.hom

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_finite : IsFinite (B.polarizationMap hrigid).left := by
  have : IsFinite (B.abelianCover ≫ (B.polarizationMap hrigid).left) := by
    rw [B.polarizationMap_cover]
    infer_instance
  exact Proper.FiniteCoverDescent.isFinite_of_proper_surjective_composite B.abelianCover (B.polarizationMap hrigid).left

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_flat : Flat (B.polarizationMap hrigid).left :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Flat) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (B.polarizationMap_cartesian hrigid).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    (inferInstanceAs (Flat ((Over.pullback b).map U.prescribedPolarization).left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_surjective : Surjective (B.polarizationMap hrigid).left := by
  have : Surjective (B.abelianCover ≫ (B.polarizationMap hrigid).left) := by
    rw [B.polarizationMap_cover]
    infer_instance
  exact Surjective.of_comp B.abelianCover (B.polarizationMap hrigid).left

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationIsogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B.abelian B.dual where
  hom := B.polarizationMap hrigid
  preservesGroup := inferInstance
  finite := inferInstance
  flat := inferInstance
  surjective := inferInstance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
