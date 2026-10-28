import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap

/-! # Action Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The coefficient endomorphism and its map on the actual prescribed
abelian overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedAction (r : NumberField.RingOfIntegers E) : U.prescribedTotalSpace ⟶ U.prescribedTotalSpace :=
  (Over.map X.hom).map (U.forgetAuxiliary.data.action.map r)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedAction_projection (r : NumberField.RingOfIntegers E) :
    U.prescribedAction r ≫ U.prescribedProjection = U.prescribedProjection :=
  Over.OverMorphism.ext (U.forgetAuxiliary.data.action.map r).w

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedActionOverlap (π : X ⟶ Q) (r : NumberField.RingOfIntegers E) :
    U.prescribedOverlap π ⟶ U.prescribedOverlap π :=
  DescentCocycleMap.DescentCocycle.map π U.prescribedProjection U.prescribedProjection
    (U.prescribedAction r) (U.prescribedAction_projection r)

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedActionOverlap_source (π : X ⟶ Q) (r : NumberField.RingOfIntegers E) :
    U.prescribedActionOverlap π r ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedAction r :=
  DescentCocycleMap.DescentCocycle.map_source _ _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedActionOverlap_base (π : X ⟶ Q) (r : NumberField.RingOfIntegers E) :
    U.prescribedActionOverlap π r ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedProjection :=
  DescentCocycleMap.DescentCocycle.map_base _ _ _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
