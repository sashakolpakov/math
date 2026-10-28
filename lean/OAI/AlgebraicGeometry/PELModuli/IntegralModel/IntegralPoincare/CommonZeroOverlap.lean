import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.DualZeroOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.OriginFrame

/-! # Common Zero Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The two origin paths agree on the actual PEL relation, giving
the commutative square required for restricting the normalization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} [NeZero L] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    [IsReduced X.left]
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.IsFine) (π : X ⟶ Q)
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincare_commonZeroOverlap :
    U.prescribedZeroOverlap hU π hk ≫ U.prescribedPoincareDualZeroOverlap π =
      U.prescribedDualZeroOverlap hU π hk ≫ U.prescribedPoincareZeroOverlap π := by
  apply pullback.hom_ext
  · change (_ ≫ U.prescribedPoincareDualZeroOverlap π) ≫
        DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection =
      (_ ≫ U.prescribedPoincareZeroOverlap π) ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
    rw [Category.assoc, U.prescribedPoincareDualZeroOverlap_source, ← Category.assoc,
      U.prescribedZeroOverlap_source, Category.assoc, U.prescribedPoincare_commonZero,
      ← Category.assoc, ← U.prescribedDualZeroOverlap_source, Category.assoc,
      ← U.prescribedPoincareZeroOverlap_source, ← Category.assoc]
  · change (_ ≫ U.prescribedPoincareDualZeroOverlap π) ≫
        DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection =
      (_ ≫ U.prescribedPoincareZeroOverlap π) ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection
    rw [Category.assoc, U.prescribedPoincareDualZeroOverlap_base,
      U.prescribedZeroOverlap_base, Category.assoc, U.prescribedPoincareZeroOverlap_base,
      U.prescribedDualZeroOverlap_base]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
