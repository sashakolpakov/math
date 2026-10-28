import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralDual.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.TotalSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleMap

/-! # Polarization Overlap -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual prescribed polarization and its map from the abelian
overlap to the dual overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s L N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R} {X Q : Over (Spec (.of R))}
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X)

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarization : U.prescribedTotalSpace ⟶ U.prescribedDualTotalSpace :=
  (Over.map X.hom).map U.forgetAuxiliary.data.polarized.polarization.isogeny.hom

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarization_projection :
    U.prescribedPolarization ≫ U.prescribedDualProjection = U.prescribedProjection :=
  Over.OverMorphism.ext U.forgetAuxiliary.data.polarized.polarization.isogeny.hom.w

def IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarizationOverlap (π : X ⟶ Q) : U.prescribedOverlap π ⟶ U.prescribedDualOverlap π :=
  DescentCocycleMap.DescentCocycle.map π U.prescribedProjection U.prescribedDualProjection
    U.prescribedPolarization U.prescribedPolarization_projection

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarizationOverlap_source (π : X ⟶ Q) :
    U.prescribedPolarizationOverlap π ≫ DescentCocycleChange.DescentCocycle.source π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.source π U.prescribedProjection ≫ U.prescribedPolarization :=
  DescentCocycleMap.DescentCocycle.map_source _ _ _ _ _

theorem IntegralAdded.PELId.IntegralAddedPELLevel.prescribedPolarizationOverlap_base (π : X ⟶ Q) :
    U.prescribedPolarizationOverlap π ≫ DescentCocycleChange.DescentCocycle.base π U.prescribedDualProjection =
      DescentCocycleChange.DescentCocycle.base π U.prescribedProjection :=
  DescentCocycleMap.DescentCocycle.map_base _ _ _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
