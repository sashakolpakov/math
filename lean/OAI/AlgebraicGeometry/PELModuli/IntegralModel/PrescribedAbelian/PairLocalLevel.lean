import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairLevelSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairIntrinsicComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.ScalarSectionComparison

/-! # Pair Local Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The original prescribed level on the cover, expressed on the actual
arithmetic abelian scheme in the native pullback convention. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localLevel : (B.abelian.pullback ((Over.pullback b).map π).left).FullLevel N :=
  AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.FullLevel.transport
    (A := U.forgetAuxiliary.data.polarized.abelian.pullback (pullback.fst X.hom b))
    (B := B.abelian.pullback ((Over.pullback b).map π).left)
    (U.forgetAuxiliary.data.polarized.level.pullback (pullback.fst X.hom b)) B.abelianNativeComparison

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.localLevelSection_cover (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    (LevelSections.fullLevelSection B.localLevel c).left ≫
      pullback.fst B.abelian.scheme.hom ((Over.pullback b).map π).left =
      ((Over.pullback b).map (U.prescribedLevelPoint c)).left ≫ B.abelianCover := by
  let A := U.forgetAuxiliary.data.polarized.abelian
  let e := Relative.ScalarIntrinsicComparison.relativeScalarNativeComparison b X A.scheme
  let z := ((Over.pullback b).map (U.prescribedLevelPoint c)).left
  have hz : z ≫ e.hom.left =
      (LevelSections.fullLevelSection (U.forgetAuxiliary.data.polarized.level.pullback (pullback.fst X.hom b)) c).left := by
    exact (Relative.ScalarSectionComparison.relativeScalarSection_native b X A.scheme
      (LevelSections.fullLevelSection U.forgetAuxiliary.data.polarized.level c)
      (U.prescribedLevelPoint c) rfl (U.prescribedLevelPoint_projection c)).trans
      (congrArg Over.Hom.left (Group.SectionPullback.fullLevelSection_pullback (pullback.fst X.hom b) A
        U.forgetAuxiliary.data.polarized.level c))
  change ((LevelSections.fullLevelSection (U.forgetAuxiliary.data.polarized.level.pullback
    (pullback.fst X.hom b)) c).left ≫ (e.inv ≫ B.abelianComparison.hom).left) ≫ _ = z ≫ _
  rw [← hz]
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc e.hom.left e.inv.left, ← Over.comp_left, e.hom_inv_id,
    Over.id_left, Category.id_comp, B.abelianComparison_cover]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.levelSection_pullback [Surjective π.left] (hrigid : U.PrescribedRigid)
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod N)) :
    Group.SectionPullback.groupSectionPullback B.abelian.scheme ((Over.pullback b).map π).left (B.levelSection hrigid c) =
      LevelSections.fullLevelSection B.localLevel c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Group.SectionPullback.groupSectionPullback_fst B.abelian.scheme _ _).trans
      ((B.levelSection_cover hrigid c).trans (B.localLevelSection_cover c).symm)
  · exact (Group.SectionPullback.groupSectionPullback B.abelian.scheme _ _).w.trans (LevelSections.fullLevelSection B.localLevel c).w.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
