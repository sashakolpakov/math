import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.PointEquations
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # Total Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual total space of the prescribed universal abelian family
and its overlap transport over the constructed arithmetic quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTotalSpace : Over (Spec (.of R)) :=
  Over.mk (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ X.hom)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedProjection : U.prescribedTotalSpace ⟶ X :=
  Over.homMk U.forgetAuxiliary.data.polarized.abelian.scheme.hom rfl

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedTotalSpace_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced U.prescribedTotalSpace.left :=
  AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource U.forgetAuxiliary.data.polarized.abelian.scheme.hom

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlap (π : X ⟶ Q) := DescentCocycleChange.DescentCocycle.overlap π U.prescribedProjection

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlap_source_finite (π : X ⟶ Q) [IsFinite π.left] :
    IsFinite (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left := by
  have h := (IsPullback.of_hasPullback (U.prescribedProjection ≫ π) π).map (Over.forget _)
  exact MorphismProperty.of_isPullback h.flip (inferInstanceAs (IsFinite π.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlap_source_etale (π : X ⟶ Q) [Etale π.left] :
    Etale (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left := by
  have h := (IsPullback.of_hasPullback (U.prescribedProjection ≫ π) π).map (Over.forget _)
  exact MorphismProperty.of_isPullback h.flip (inferInstanceAs (Etale π.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlap_reduced [IsReduced X.left] [IsLocallyNoetherian X.left]
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] : IsReduced (U.prescribedOverlap π).left :=
  Finite.EtaleReduced.finite_etale_isReduced (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapTarget : U.prescribedOverlap π ⟶ U.prescribedTotalSpace := by
  let f := DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedProjection
  let h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedProjection
  let t := U.prescribedPointTransport hU π hk f g h
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left rfl
  have ht : t ≫ U.forgetAuxiliary.data.polarized.abelian.scheme.hom = g.left :=
    U.prescribedPointTransport_base hU π hk f g h _ rfl
  exact Over.homMk t (by
    change t ≫ (U.forgetAuxiliary.data.polarized.abelian.scheme.hom ≫ X.hom) = _
    rw [← Category.assoc, ht]
    exact g.w)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedOverlapTarget_base :
    U.prescribedOverlapTarget hU π hk ≫ U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedProjection := by
  apply Over.OverMorphism.ext
  exact U.prescribedPointTransport_base hU π hk
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedProjection)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedProjection)
    (DescentCocycleChange.DescentCocycle.source_condition π U.prescribedProjection)
    (DescentCocycleChange.DescentCocycle.source π U.prescribedProjection).left rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
