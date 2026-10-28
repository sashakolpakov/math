import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.PairZero
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.ZeroOverlap

/-! # Pair Zero Square -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual abelian zero section commutes with the product quotient
and the dual-family cover. -/

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

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroSection : B.dual.scheme.left ⟶ B.productTotal.left :=
  (lift (𝟙 B.dual.scheme) (1 : B.dual.scheme ⟶ B.abelian.scheme)).left

omit [Surjective π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroSection_dual : B.abelianZeroSection ≫ (fst B.dual.scheme B.abelian.scheme).left = 𝟙 _ :=
  congrArg Over.Hom.left (lift_fst (𝟙 B.dual.scheme) (1 : B.dual.scheme ⟶ B.abelian.scheme))

omit [Surjective π.left] in
theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroSection_abelian : B.abelianZeroSection ≫ (snd B.dual.scheme B.abelian.scheme).left =
    B.dual.scheme.hom ≫ (MonObj.one : 𝟙_ (Over ((Over.pullback b).obj Q).left) ⟶ B.abelian.scheme).left := by
  exact congrArg Over.Hom.left (lift_snd (𝟙 B.dual.scheme) (1 : B.dual.scheme ⟶ B.abelian.scheme))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_abelianZero : ((Over.pullback b).map U.prescribedPoincareZero).left ≫ B.productCover =
    B.dualCover ≫ B.abelianZeroSection := by
  let F := Over.pullback b
  have hzD := congrArg (fun f => (F.map f).left) U.prescribedPoincareZero_dual
  simp only [F.map_comp, F.map_id, Over.comp_left, Over.id_left] at hzD
  have hzA := congrArg (fun f => (F.map f).left) U.prescribedPoincareZero_abelian
  simp only [F.map_comp, Over.comp_left] at hzA
  apply pullback.hom_ext
  · change (_ ≫ B.productCover) ≫ (fst B.dual.scheme B.abelian.scheme).left =
      (B.dualCover ≫ B.abelianZeroSection) ≫ (fst B.dual.scheme B.abelian.scheme).left
    rw [Category.assoc, B.productCover_dual, ← Category.assoc, hzD, Category.id_comp,
      Category.assoc, B.abelianZeroSection_dual, Category.comp_id]
  · change (_ ≫ B.productCover) ≫ (snd B.dual.scheme B.abelian.scheme).left =
      (B.dualCover ≫ B.abelianZeroSection) ≫ (snd B.dual.scheme B.abelian.scheme).left
    rw [Category.assoc, B.productCover_abelian, ← Category.assoc, hzA, Category.assoc,
      B.abelianCover_zero, ← Category.assoc, B.dualCartesian.w,
      Category.assoc, Category.assoc, B.abelianZeroSection_abelian]

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualTotal : Over S := (Over.map ((Over.pullback b).obj Q).hom).obj B.dual.scheme

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.dualCoverOver : (Over.pullback b).obj U.prescribedDualTotalSpace ⟶ B.dualTotal :=
  Over.homMk B.dualCover (by
    change B.dualCover ≫ (B.dual.scheme.hom ≫ ((Over.pullback b).obj Q).hom) = _
    rw [← Category.assoc, ← B.dualCartesian.w, Category.assoc, Over.w, Over.w])

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZeroOver : B.dualTotal ⟶ B.productTotal :=
  (Over.map ((Over.pullback b).obj Q).hom).map (lift (𝟙 B.dual.scheme) (1 : B.dual.scheme ⟶ B.abelian.scheme))

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.abelianZero_square : (Over.pullback b).map U.prescribedPoincareZero ≫ B.productCoverOver =
    B.dualCoverOver ≫ B.abelianZeroOver := Over.OverMorphism.ext B.productCover_abelianZero

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
