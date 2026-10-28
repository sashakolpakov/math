import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PairSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RelationLift

/-! # Pair Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The relative pair family inherits the actual prescribed transport
relation, with its two component maps into the original relation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (π : X ⟶ Q)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlap := DescentCocycleChange.DescentCocycle.overlap π U.prescribedPairProjection

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapFst : U.prescribedPairOverlap π ⟶ U.prescribedOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedPairFst)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedPairProjection)
    (by simpa only [Category.assoc] using DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPairProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapSnd : U.prescribedPairOverlap π ⟶ U.prescribedOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedPairSnd)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedPairProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedPairSnd, U.prescribedPairSnd_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPairProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedMulOverlap : U.prescribedPairOverlap π ⟶ U.prescribedOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedMul)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedPairProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedMul, U.prescribedMul_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedPairProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapFst_source :
    U.prescribedPairOverlapFst π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedPairFst := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapSnd_source :
    U.prescribedPairOverlapSnd π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedPairSnd := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedMulOverlap_source :
    U.prescribedMulOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection ≫ U.prescribedMul := pullback.lift_fst _ _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlap_reduced [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsFinite π.left] [Etale π.left] : IsReduced (U.prescribedPairOverlap π).left := by
  let f := DescentCocycleChange.DescentCocycle.source π U.prescribedPairProjection
  have h := (IsPullback.of_hasPullback (U.prescribedPairProjection ≫ π) π).map (Over.forget _)
  have : IsFinite f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (IsFinite π.left))
  have : Etale f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (Etale π.left))
  exact Finite.EtaleReduced.finite_etale_isReduced f.left

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairTarget : U.prescribedPairOverlap π ⟶ U.prescribedPairSpace :=
  U.prescribedPair_square.lift
    (U.prescribedPairOverlapFst π ≫ U.prescribedOverlapTarget hU π hk)
    (U.prescribedPairOverlapSnd π ≫ U.prescribedOverlapTarget hU π hk) (by
      simp only [Category.assoc, U.prescribedOverlapTarget_base,
        IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapFst, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairOverlapSnd, DescentCocycleChange.DescentCocycle.base, pullback.lift_snd])

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairTarget_fst : U.prescribedPairTarget π hU hk ≫ U.prescribedPairFst =
    U.prescribedPairOverlapFst π ≫ U.prescribedOverlapTarget hU π hk :=
  U.prescribedPair_square.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairTarget_snd : U.prescribedPairTarget π hU hk ≫ U.prescribedPairSnd =
    U.prescribedPairOverlapSnd π ≫ U.prescribedOverlapTarget hU π hk :=
  U.prescribedPair_square.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPairTarget_projection :
    U.prescribedPairTarget π hU hk ≫ U.prescribedPairProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedPairProjection := by
  change _ ≫ U.prescribedPairFst ≫ U.prescribedProjection = _
  rw [← Category.assoc, U.prescribedPairTarget_fst, Category.assoc, U.prescribedOverlapTarget_base]
  exact pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
