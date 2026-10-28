import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.PairSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.RelationLift

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

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlap := DescentCocycleChange.DescentCocycle.overlap π U.prescribedDualPairProjection

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapFst : U.prescribedDualPairOverlap π ⟶ U.prescribedDualOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualPairFst)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualPairProjection)
    (by simpa only [Category.assoc] using DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualPairProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapSnd : U.prescribedDualPairOverlap π ⟶ U.prescribedDualOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualPairSnd)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualPairProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedDualPairSnd, U.prescribedDualPairSnd_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualPairProjection)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualMulOverlap : U.prescribedDualPairOverlap π ⟶ U.prescribedDualOverlap π :=
  pullback.lift (DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualMul)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualPairProjection) (by
      rw [Category.assoc, ← Category.assoc U.prescribedDualMul, U.prescribedDualMul_projection]
      exact DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualPairProjection)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapFst_source :
    U.prescribedDualPairOverlapFst π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualPairFst := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapSnd_source :
    U.prescribedDualPairOverlapSnd π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualPairSnd := pullback.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualMulOverlap_source :
    U.prescribedDualMulOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection ≫ U.prescribedDualMul := pullback.lift_fst _ _ _

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlap_reduced [IsReduced X.left] [IsLocallyNoetherian X.left]
    [IsFinite π.left] [Etale π.left] : IsReduced (U.prescribedDualPairOverlap π).left := by
  let f := DescentCocycleChange.DescentCocycle.source π U.prescribedDualPairProjection
  have h := (IsPullback.of_hasPullback (U.prescribedDualPairProjection ≫ π) π).map (Over.forget _)
  have : IsFinite f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (IsFinite π.left))
  have : Etale f.left := MorphismProperty.of_isPullback h.flip (inferInstanceAs (Etale π.left))
  exact Finite.EtaleReduced.finite_etale_isReduced f.left

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairTarget : U.prescribedDualPairOverlap π ⟶ U.prescribedDualPairSpace :=
  U.prescribedDualPair_square.lift
    (U.prescribedDualPairOverlapFst π ≫ U.prescribedDualOverlapTarget hU π hk)
    (U.prescribedDualPairOverlapSnd π ≫ U.prescribedDualOverlapTarget hU π hk) (by
      simp only [Category.assoc, U.prescribedDualOverlapTarget_base,
        IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapFst, IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairOverlapSnd, DescentCocycleChange.DescentCocycle.base, pullback.lift_snd])

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairTarget_fst : U.prescribedDualPairTarget π hU hk ≫ U.prescribedDualPairFst =
    U.prescribedDualPairOverlapFst π ≫ U.prescribedDualOverlapTarget hU π hk :=
  U.prescribedDualPair_square.lift_fst _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairTarget_snd : U.prescribedDualPairTarget π hU hk ≫ U.prescribedDualPairSnd =
    U.prescribedDualPairOverlapSnd π ≫ U.prescribedDualOverlapTarget hU π hk :=
  U.prescribedDualPair_square.lift_snd _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualPairTarget_projection :
    U.prescribedDualPairTarget π hU hk ≫ U.prescribedDualPairProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedDualPairProjection := by
  change _ ≫ U.prescribedDualPairFst ≫ U.prescribedDualProjection = _
  rw [← Category.assoc, U.prescribedDualPairTarget_fst, Category.assoc, U.prescribedDualOverlapTarget_base]
  exact pullback.lift_snd _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
