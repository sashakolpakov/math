import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.Point
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # Total Space -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual total space of the prescribed universal dual abelian family
and its overlap transport over the constructed arithmetic quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualTotalSpace : Over (Spec (.of R)) :=
  Over.mk (U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom ≫ X.hom)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualProjection : U.prescribedDualTotalSpace ⟶ X :=
  Over.homMk U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom rfl

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualTotalSpace_reduced [IsReduced X.left] [IsLocallyNoetherian X.left] :
    IsReduced U.prescribedDualTotalSpace.left :=
  AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom

abbrev IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlap (π : X ⟶ Q) := DescentCocycleChange.DescentCocycle.overlap π U.prescribedDualProjection

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlap_source_finite (π : X ⟶ Q) [IsFinite π.left] :
    IsFinite (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left := by
  have h := (IsPullback.of_hasPullback (U.prescribedDualProjection ≫ π) π).map (Over.forget _)
  exact MorphismProperty.of_isPullback h.flip (inferInstanceAs (IsFinite π.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlap_source_etale (π : X ⟶ Q) [Etale π.left] :
    Etale (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left := by
  have h := (IsPullback.of_hasPullback (U.prescribedDualProjection ≫ π) π).map (Over.forget _)
  exact MorphismProperty.of_isPullback h.flip (inferInstanceAs (Etale π.left))

instance IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlap_reduced [IsReduced X.left] [IsLocallyNoetherian X.left]
    (π : X ⟶ Q) [IsFinite π.left] [Etale π.left] : IsReduced (U.prescribedDualOverlap π).left :=
  Finite.EtaleReduced.finite_etale_isReduced (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left

variable [NeZero L] [IsReduced X.left] [IsLocallyNoetherian X.left]
    (hU : U.IsFine) (π : X ⟶ Q) [IsFinite π.left] [Etale π.left]
    (hk : IsKernelPair π.left (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.source X (3 * s) L).left
      (IntegralAuxiliary.ActionSpace.IntegralAuxiliaryAction.target U hU).left)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlapTarget : U.prescribedDualOverlap π ⟶ U.prescribedDualTotalSpace := by
  let f := DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection
  let g := DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection
  let h : f ≫ π = g ≫ π := DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection
  let t := U.prescribedDualPointTransport hU π hk f g h
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left rfl
  have ht : t ≫ U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom = g.left :=
    U.prescribedDualPointTransport_base hU π hk f g h _ rfl
  exact Over.homMk t (by
    change t ≫ (U.forgetAuxiliary.data.polarized.dual.abelian.scheme.hom ≫ X.hom) = _
    rw [← Category.assoc, ht]
    exact g.w)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedDualOverlapTarget_base :
    U.prescribedDualOverlapTarget hU π hk ≫ U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection := by
  apply Over.OverMorphism.ext
  exact U.prescribedDualPointTransport_base hU π hk
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection ≫ U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.source_condition π U.prescribedDualProjection)
    (DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection).left rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
