import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPoincare.Space
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.RelationLift
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RelationLift

/-! # Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The Poincare product carries the actual dual and abelian overlap
transports, over the common prescribed-level quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlap := DescentCocycleChange.DescentCocycle.overlap π U.prescribedPoincareProjection

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual : U.prescribedPoincareOverlap π ⟶ U.prescribedDualOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection ≫ U.prescribedPoincareDual)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection)
    (by simpa only [Category.assoc] using DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPoincareProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapAbelian : U.prescribedPoincareOverlap π ⟶ U.prescribedOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection ≫ U.prescribedPoincareAbelian)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedPoincareAbelian,
        U.prescribedPoincareAbelian_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPoincareProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual_source :
    U.prescribedPoincareOverlapDual π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection ≫ U.prescribedPoincareDual :=
  pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapAbelian_source :
    U.prescribedPoincareOverlapAbelian π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection ≫ U.prescribedPoincareAbelian :=
  pullback.lift_fst _ _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlap_reduced [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsFinite π.left] [Etale π.left] : IsReduced (U.prescribedPoincareOverlap π).left := by
  let f := DescentCocycleChange.DescentCocycle.source π U.prescribedPoincareProjection
  have h := (IsPullback.of_hasPullback (U.prescribedPoincareProjection ≫ π) π).map (Over.forget _)
  have : IsFinite f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (IsFinite π.left))
  have : Etale f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (Etale π.left))
  exact Finite.EtaleReduced.finite_etale_isReduced f.left

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget : U.prescribedPoincareOverlap π ⟶ U.prescribedPoincareSpace :=
  U.prescribedPoincare_square.lift
    (U.prescribedPoincareOverlapDual π ≫ U.prescribedDualOverlapTarget hU π hk)
    (U.prescribedPoincareOverlapAbelian π ≫ U.prescribedOverlapTarget hU π hk) (by
      simp only [Category.assoc, U.prescribedDualOverlapTarget_base, U.prescribedOverlapTarget_base,
        IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapDual, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareOverlapAbelian,
        DescentCocycleChange.DescentCocycle.base, pullback.lift_snd])

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget_dual :
    U.prescribedPoincareTarget π hU hk ≫ U.prescribedPoincareDual =
      U.prescribedPoincareOverlapDual π ≫ U.prescribedDualOverlapTarget hU π hk :=
  U.prescribedPoincare_square.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget_abelian :
    U.prescribedPoincareTarget π hU hk ≫ U.prescribedPoincareAbelian =
      U.prescribedPoincareOverlapAbelian π ≫ U.prescribedOverlapTarget hU π hk :=
  U.prescribedPoincare_square.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPoincareTarget_projection :
    U.prescribedPoincareTarget π hU hk ≫ U.prescribedPoincareProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedPoincareProjection := by
  change _ ≫ U.prescribedPoincareDual ≫ U.prescribedDualProjection = _
  rw [← Category.assoc, U.prescribedPoincareTarget_dual, Category.assoc,
    U.prescribedDualOverlapTarget_base]
  exact pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
