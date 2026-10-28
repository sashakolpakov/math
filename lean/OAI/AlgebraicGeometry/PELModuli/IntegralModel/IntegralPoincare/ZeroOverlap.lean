import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Relation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.ZeroRelation

/-! # Zero Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The abelian zero section gives an actual section of the Poincare
overlap over the dual overlap, with its original source and base maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero_projection :
    U.prescribedPoincareZero ≫ U.prescribedPoincareProjection = U.prescribedDualProjection := by
  change _ ≫ U.prescribedPoincareDual ≫ U.prescribedDualProjection = _
  rw [← Category.assoc, U.prescribedPoincareZero_dual, Category.id_comp]

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero_abelian :
    U.prescribedPoincareZero ≫ U.prescribedPoincareAbelian =
      U.prescribedDualProjection ≫ U.prescribedZero := by
  unfold IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZero IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareAbelian
  rw [← (Over.map X.hom).map_comp, lift_snd]
  apply Over.OverMorphism.ext
  rfl

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZeroOverlap (π : X ⟶ Q) :
    U.prescribedDualOverlap π ⟶ U.prescribedPoincareOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedPoincareZero)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedPoincareZero, U.prescribedPoincareZero_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZeroOverlap_source (π : X ⟶ Q) :
    U.prescribedPoincareZeroOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedPoincareZero :=
  pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZeroOverlap_base (π : X ⟶ Q) :
    U.prescribedPoincareZeroOverlap π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection := pullback.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareZeroOverlap_dual (π : X ⟶ Q) :
    U.prescribedPoincareZeroOverlap π ≫ U.prescribedPoincareOverlapDual π =
      𝟙 (U.prescribedDualOverlap π) := by
  apply pullback.hom_ext
  · change (_ ≫ U.prescribedPoincareOverlapDual π) ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection = _
    rw [Category.assoc, U.prescribedPoincareOverlapDual_source, ← Category.assoc,
      U.prescribedPoincareZeroOverlap_source, Category.assoc, U.prescribedPoincareZero_dual,
      Category.comp_id, Category.id_comp]
  · change (_ ≫ U.prescribedPoincareOverlapDual π) ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection = _
    simp only [Category.assoc, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual, DescentCocycleChange.DescentCocycle.base,
      pullback.lift_snd, Category.id_comp]
    exact U.prescribedPoincareZeroOverlap_base π

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
