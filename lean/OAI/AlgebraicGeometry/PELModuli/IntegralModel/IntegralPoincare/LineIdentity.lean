import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.NormalizedRestriction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Triple
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.PoincareZeroGeometry

/-! # Line Identity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Restriction of the constructed normalized Poincare isomorphism to
the diagonal is the actual identity. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine)
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left) (hrigid : U.PrescribedRigid)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareNormalizedIso_identity :
    LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine
      (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
      (U.prescribedPoincareTarget π hU hk).left
      (DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection).left
      (𝟙 U.prescribedPoincareSpace.left) (𝟙 U.prescribedPoincareSpace.left)
      (congrArg Over.Hom.left (DescentCocycleChange.DescentCocycle.diagonal_source π U.prescribedPoincareProjection))
      (congrArg Over.Hom.left (U.prescribedPoincareTarget_normalized hU π hk hrigid))
      (U.prescribedPoincareNormalizedIso hU π hk hrigid) =
        CategoryTheory.Iso.refl (U.prescribedPoincareLine.pullback (𝟙 U.prescribedPoincareSpace.left)).sheaf := by
  let e := LineBundle.NormalizedRestriction.lineBundleRestrictIso U.prescribedPoincareLine
    (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection).left
    (U.prescribedPoincareTarget π hU hk).left
    (DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection).left
    (𝟙 U.prescribedPoincareSpace.left) (𝟙 U.prescribedPoincareSpace.left)
    (congrArg Over.Hom.left (DescentCocycleChange.DescentCocycle.diagonal_source π U.prescribedPoincareProjection))
    (congrArg Over.Hom.left (U.prescribedPoincareTarget_normalized hU π hk hrigid))
    (U.prescribedPoincareNormalizedIso hU π hk hrigid)
  have hw : U.prescribedPoincareZero ≫ 𝟙 _ = (𝟙 _) ≫ U.prescribedPoincareZero := by simp
  let F := LineBundle.SquareFrame.lineBundleSquareFrame U.prescribedPoincareLine U.prescribedPoincareZero.left
    U.prescribedPoincareFrame (𝟙 U.prescribedPoincareSpace.left) U.prescribedPoincareZero.left
      (𝟙 U.prescribedDualTotalSpace.left) (congrArg Over.Hom.left hw)
  have he : (Scheme.Modules.pullback U.prescribedPoincareZero.left).mapIso e ≪≫ F = F :=
    U.prescribedPoincareNormalizedIso_restrict hU π hk hrigid
      (DescentCocycleChange.DescentCocycle.diagonal π U.prescribedPoincareProjection) U.prescribedPoincareZero
      (DescentCocycleChange.DescentCocycle.diagonal π U.prescribedDualProjection) (U.prescribedPoincareZero_diagonal π)
      (𝟙 _) (𝟙 _) (𝟙 _) (𝟙 _)
      (DescentCocycleChange.DescentCocycle.diagonal_source π U.prescribedPoincareProjection)
      (U.prescribedPoincareTarget_normalized hU π hk hrigid)
      (DescentCocycleChange.DescentCocycle.diagonal_source π U.prescribedDualProjection)
      (U.prescribedDualOverlapTarget_normalized hU π hk hrigid) hw hw
  change e = CategoryTheory.Iso.refl _
  apply Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.normalizedIso_unique U.prescribedPoincareDual.left
    U.prescribedPoincareZero.left (congrArg Over.Hom.left U.prescribedPoincareZero_dual)
    U.prescribedPoincare_globalFunctions
    (U.prescribedPoincareLine.pullback (𝟙 U.prescribedPoincareSpace.left)).locallyTrivial F F
  · exact congrArg Iso.hom he
  · change (Scheme.Modules.pullback U.prescribedPoincareZero.left).map (𝟙 _) ≫ F.hom = F.hom
    exact (congrArg (fun m => m ≫ F.hom)
      ((Scheme.Modules.pullback U.prescribedPoincareZero.left).map_id _)).trans (Category.id_comp _)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
