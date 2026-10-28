import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityBaseChange

/-! # Rigidity Scalar Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityScalarChange

noncomputable section

/-! Actual prescribed-level rigidity persists under every coefficient
change, by regarding each reduced test scheme over the original ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s L N : ℕ}
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* R}
    {X : Over (Spec (.of R))}

theorem integralAddedPEL_prescribedRigid_baseChange
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P R iotaO L N X) (hU : U.PrescribedRigid)
    (φ : R →+* R') : (U.baseChange φ).PrescribedRigid := by
  apply RigidityBaseChange.integralAddedPEL_prescribedRigid_baseChange_of_away U 1 ?_ φ (by
    rw [map_one]
    exact isUnit_one)
  intro T _ e _
  let T' : Over (Spec (.of R)) := Over.mk (T.hom ≫ X.hom)
  have : IsReduced T'.left := inferInstanceAs (IsReduced T.left)
  exact hU T' (Over.homMk T.hom rfl) e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityScalarChange
