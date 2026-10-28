import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairPolarizationCartesian
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyMorphismComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent

/-! # Pair Polarization Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The descended polarization recovers the original scalar morphism
under the prescribed cartesian group comparisons, hence is a group map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_comparison :
    B.abelianComparison.hom ≫ (Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid) =
      (Relative.ScalarFunctor.relativeScalarFunctor b X).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom ≫
        B.dualComparison.hom :=
  Cartesian.FamilyMorphismComparison.cartesian_family_morphism_comparison ((Over.pullback b).map π).left _ _
    B.abelian.scheme B.dual.scheme B.abelianComparison B.dualComparison
    B.abelianCover B.dualCover B.abelianComparison_cover B.dualComparison_cover
    ((Relative.ScalarFunctor.relativeScalarFunctor b X).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom)
    (B.polarizationMap hrigid) (B.polarizationMap_cover hrigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_image :
    (Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid) =
      B.abelianComparison.inv ≫
        (Relative.ScalarFunctor.relativeScalarFunctor b X).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom ≫
          B.dualComparison.hom :=
  Cartesian.FamilyMorphismComparison.cartesian_family_morphism_image ((Over.pullback b).map π).left _ _ _ _
    B.abelianComparison B.dualComparison _ _ (B.polarizationMap_comparison hrigid)

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.polarizationMap_group : IsMonHom (B.polarizationMap hrigid) := by
  have : Etale ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Etale π.left))
  have : Surjective ((Over.pullback b).map π).left :=
    MorphismProperty.of_isPullback (Specialization.base_change_square b π) (inferInstanceAs (Surjective π.left))
  have := B.abelianComparison_group
  have := B.dualComparison_group
  have : IsMonHom ((Over.pullback ((Over.pullback b).map π).left).map (B.polarizationMap hrigid)) := by
    rw [B.polarizationMap_image]
    infer_instance
  exact ActionDescent.isMonHom_of_faithful_map (Over.pullback ((Over.pullback b).map π).left) (B.polarizationMap hrigid)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
