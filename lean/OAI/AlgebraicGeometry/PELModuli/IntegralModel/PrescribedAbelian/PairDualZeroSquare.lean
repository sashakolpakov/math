import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZero
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualZero

/-! # Pair Dual Zero Square -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual dual-zero section commutes with the product quotient
and the abelian-family cover. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroSection : B.abelian.scheme.left ⟶ B.productTotal.left :=
  (lift (1 : B.abelian.scheme ⟶ B.dual.scheme) (𝟙 B.abelian.scheme)).left

omit [Surjective π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroSection_abelian : B.dualZeroSection ≫ (snd B.dual.scheme B.abelian.scheme).left = 𝟙 _ :=
  congrArg Over.Hom.left (lift_snd (1 : B.abelian.scheme ⟶ B.dual.scheme) (𝟙 B.abelian.scheme))

omit [Surjective π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualZeroSection_dual : B.dualZeroSection ≫ (fst B.dual.scheme B.abelian.scheme).left =
    B.abelian.scheme.hom ≫ (MonObj.one : 𝟙_ (Over ((Over.pullback b).obj Q).left) ⟶ B.dual.scheme).left := by
  exact congrArg Over.Hom.left (lift_fst (1 : B.abelian.scheme ⟶ B.dual.scheme) (𝟙 B.abelian.scheme))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_dualZero : ((Over.pullback b).map U.prescribedPoincareDualZero).left ≫ B.productCover =
    B.abelianCover ≫ B.dualZeroSection := by
  let F := Over.pullback b
  have hzA := congrArg (fun f => (F.map f).left) U.prescribedPoincareDualZero_abelian
  simp only [F.map_comp, F.map_id, Over.comp_left, Over.id_left] at hzA
  have hzD := congrArg (fun f => (F.map f).left) U.prescribedPoincareDualZero_dual
  simp only [F.map_comp, Over.comp_left] at hzD
  apply pullback.hom_ext
  · change (_ ≫ B.productCover) ≫ (fst B.dual.scheme B.abelian.scheme).left =
      (B.abelianCover ≫ B.dualZeroSection) ≫ (fst B.dual.scheme B.abelian.scheme).left
    rw [Category.assoc, B.productCover_dual, ← Category.assoc, hzD, Category.assoc,
      B.dualCover_zero, ← Category.assoc, B.abelianCartesian.w,
      Category.assoc, Category.assoc, B.dualZeroSection_dual]
  · change (_ ≫ B.productCover) ≫ (snd B.dual.scheme B.abelian.scheme).left =
      (B.abelianCover ≫ B.dualZeroSection) ≫ (snd B.dual.scheme B.abelian.scheme).left
    rw [Category.assoc, B.productCover_abelian, ← Category.assoc, hzA, Category.id_comp,
      Category.assoc, B.dualZeroSection_abelian, Category.comp_id]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
