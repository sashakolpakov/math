import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralPrescribed.RigidityBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPolarizedRigidity

/-! # Characteristic Zero Prescribed Rigidity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPrescribedRigidity

noncomputable section

/-! Prescribed-level rigidity over a countable characteristic-zero
field and every coefficient extension, including the complex numbers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s L N : ℕ}
    {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iotaO : NumberField.RingOfIntegers E →+* K}
    {X : Over (Spec (.of K))} [IsNoetherian X.left] [LocallyOfFiniteType X.hom]

theorem characteristicZero_prescribedRigid (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO L N X)
    (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0}) : U.PrescribedRigid := by
  intro T _ f e
  have : IsReduced (Over.mk f.left).left := inferInstanceAs (IsReduced T.left)
  exact CharacteristicZeroPolarizedRigidity.characteristicZero_polarized_reduced_rigidity X.hom U.forgetAuxiliary.data.polarized
    hN hPresentations (Over.mk f.left) e

theorem characteristicZero_baseChange_prescribedRigid
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P K iotaO L N X)
    (hN : 3 ≤ N)
    (hPresentations : Presentations.Hilbert.EndomorphismEquationsInput.{0})
    {R : Type} [CommRing R] (φ : K →+* R) : (U.baseChange φ).PrescribedRigid := by
  obtain ⟨r, hr, hrigid⟩ := GlobalReducedPolarizedRigidity.polarized_reduced_rigidity_away (RingHom.id K)
    Function.injective_id X.hom U.forgetAuxiliary.data.polarized hN hPresentations
  exact IntegralPrescribed.RigidityBaseChange.integralAddedPEL_prescribedRigid_baseChange_of_away U r hrigid φ
    ((isUnit_iff_ne_zero.mpr hr).map φ)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CharacteristicZeroPrescribedRigidity
