import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrescribedAbelian.Pair
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Prescribed.PoincareQuotient

/-! # Pair Product -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual pair of descended abelian schemes determines its
finite etale product cover and the exact original Poincare relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left] [IsLocallyNoetherian X.left]
    {U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X} {hU : U.IsFine}
    {π : X ⟶ Q} [IsFinite π.left] [Etale π.left] [Surjective π.left]
    {hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left} {S : Scheme.{0}} {b : S ⟶ Spec (.of R)}
    (B : U.PrescribedAbelianPair hU π hk b)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.exists_productCover :
    ∃ q : ((Over.pullback b).obj U.prescribedPoincareSpace).left ⟶ (B.dual.scheme ⊗ B.abelian.scheme).left,
      q ≫ (fst B.dual.scheme B.abelian.scheme).left = ((Over.pullback b).map U.prescribedPoincareDual).left ≫ B.dualCover ∧
      q ≫ (snd B.dual.scheme B.abelian.scheme).left = ((Over.pullback b).map U.prescribedPoincareAbelian).left ≫ B.abelianCover ∧
      IsPullback ((Over.pullback b).map U.prescribedPoincareProjection).left q
        ((Over.pullback b).map π).left (B.dual.scheme ⊗ B.abelian.scheme).hom ∧
      IsFinite q ∧ Etale q ∧ Surjective q ∧
      IsKernelPair q ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
        ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left :=
  U.prescribed_poincare_product_quotient hU π hk b B.dual.scheme B.abelian.scheme
    B.dualCover B.abelianCover B.dualCartesian B.abelianCartesian B.dualKernelPair B.abelianKernelPair

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover : ((Over.pullback b).obj U.prescribedPoincareSpace).left ⟶ (B.dual.scheme ⊗ B.abelian.scheme).left :=
  B.exists_productCover.choose

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_dual : B.productCover ≫ (fst B.dual.scheme B.abelian.scheme).left =
    ((Over.pullback b).map U.prescribedPoincareDual).left ≫ B.dualCover := B.exists_productCover.choose_spec.1

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_abelian : B.productCover ≫ (snd B.dual.scheme B.abelian.scheme).left =
    ((Over.pullback b).map U.prescribedPoincareAbelian).left ≫ B.abelianCover := B.exists_productCover.choose_spec.2.1

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_cartesian : IsPullback ((Over.pullback b).map U.prescribedPoincareProjection).left B.productCover
    ((Over.pullback b).map π).left (B.dual.scheme ⊗ B.abelian.scheme).hom := B.exists_productCover.choose_spec.2.2.1

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_finite : IsFinite B.productCover := B.exists_productCover.choose_spec.2.2.2.1
instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_etale : Etale B.productCover := B.exists_productCover.choose_spec.2.2.2.2.1
instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_surjective : Surjective B.productCover := B.exists_productCover.choose_spec.2.2.2.2.2.1

theorem IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCover_kernelPair :
    IsKernelPair B.productCover ((Over.pullback b).map (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection)).left
      ((Over.pullback b).map (U.prescribedPoincareTarget π hU hk)).left := B.exists_productCover.choose_spec.2.2.2.2.2.2

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productTotal : Over S := (Over.map ((Over.pullback b).obj Q).hom).obj (B.dual.scheme ⊗ B.abelian.scheme)

def IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productCoverOver : (Over.pullback b).obj U.prescribedPoincareSpace ⟶ B.productTotal :=
  Over.homMk B.productCover (by
    change B.productCover ≫ ((B.dual.scheme ⊗ B.abelian.scheme).hom ≫ ((Over.pullback b).obj Q).hom) = _
    rw [← Category.assoc, ← B.productCover_cartesian.w, Category.assoc, Over.w, Over.w])

instance IntegralAdded.PELId.IntegralAddedPELLevel.PrescribedAbelianPair.productTotal_locallyNoetherian [IsLocallyNoetherian ((Over.pullback b).obj Q).left] :
    IsLocallyNoetherian B.productTotal.left := by
  have : IsProper (fst B.dual.scheme B.abelian.scheme).left := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback B.dual.scheme.hom B.abelian.scheme.hom).flip
      (inferInstanceAs (IsProper B.abelian.scheme.hom))
  have : IsProper (B.dual.scheme ⊗ B.abelian.scheme).hom := by
    rw [← Over.w (fst B.dual.scheme B.abelian.scheme)]
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian (B.dual.scheme ⊗ B.abelian.scheme).hom

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
