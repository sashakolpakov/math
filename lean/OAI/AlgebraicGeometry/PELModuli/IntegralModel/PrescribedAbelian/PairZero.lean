import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairProduct
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupCoverZero

/-! # Pair Zero -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Both actual covering maps of the common-base pair preserve zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
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

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianCover_zero : ((Over.pullback b).map U.prescribedZero).left ≫ B.abelianCover =
    ((Over.pullback b).map π).left ≫ (MonObj.one : 𝟙_ (Over ((Over.pullback b).obj Q).left) ⟶ B.abelian.scheme).left := by
  have : IsMonHom B.abelianComparison.hom := B.abelianComparison_group
  have h := Cartesian.GroupCoverZero.cartesian_group_cover_zero ((Over.pullback b).map π).left
    ((Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.abelian.scheme)
    B.abelian.scheme B.abelianComparison B.abelianCover B.abelianComparison_cover
  rw [U.prescribed_scalar_one b] at h
  exact h

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualCover_zero : ((Over.pullback b).map U.prescribedDualZero).left ≫ B.dualCover =
    ((Over.pullback b).map π).left ≫ (MonObj.one : 𝟙_ (Over ((Over.pullback b).obj Q).left) ⟶ B.dual.scheme).left := by
  have : IsMonHom B.dualComparison.hom := B.dualComparison_group
  have h := Cartesian.GroupCoverZero.cartesian_group_cover_zero ((Over.pullback b).map π).left
    ((Relative.ScalarFunctor.relativeScalarFunctor b X).obj U.forgetAuxiliary.data.polarized.dual.abelian.scheme)
    B.dual.scheme B.dualComparison B.dualCover B.dualComparison_cover
  rw [U.prescribed_dual_scalar_one b] at h
  exact h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
