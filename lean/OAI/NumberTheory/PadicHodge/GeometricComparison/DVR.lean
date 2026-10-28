import OAI.NumberTheory.PadicHodge.GeometricComparison.Residue
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Foundations

/-! # DVR -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DVR.PadicBase

noncomputable section

/-! The actual split p-adic base as a complete mixed-characteristic DVR for Cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Foundations

variable (q : ℕ) [Fact q.Prime]

abbrev dvr : AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR q where
  R := ℤ_[q]
  k := ZMod q
  residueEquiv := PadicInt.residueField
  wittLift := (WittVector.equiv q).toRingHom
  wittLift_injective := (WittVector.equiv q).injective
  wittLift_residue := by
    rw [Residue.PadicBase.residueField_residue]
    exact Residue.PadicBase.wittEquiv_residue q

@[simp]
theorem reduction_eq : (dvr q).reduction = PadicInt.toZMod :=
  Residue.PadicBase.residueField_residue q

theorem specialFiber_eq (X : Over (Spec (CommRingCat.of ℤ_[q]))) :
    (dvr q).specialFiber X =
      (Over.pullback (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))).obj X :=
  congrArg (fun r : ℤ_[q] →+* ZMod q =>
    (Over.pullback (Spec.map (CommRingCat.ofHom r))).obj X) (reduction_eq q)

theorem coefficientFrobenius_eq_id :
    (dvr q).coefficientFrobenius = RingEquiv.refl (dvr q).K₀ :=
  WittFrobenius.Crystalline.fractionFrobenius_eq_id q

/-- The actual unramified coefficient inclusion is an equivalence at the split prime. -/
def unramifiedFieldEquiv : (dvr q).K₀ ≃+* (dvr q).K :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.equiv q)

theorem coefficientInclusion_eq :
    (dvr q).coefficientInclusion = (unramifiedFieldEquiv q).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Crystalline.CoefficientAdapter.Witt q)
  intro w
  rw [AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.coefficientInclusion_algebraMap]
  exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap (WittVector.equiv q) w).symm

/-- Identify the generic coefficient field with the actual Q_q used by GeometricComparison. -/
def localFieldEquiv : (dvr q).K ≃+* ℚ_[q] :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl ℤ_[q])

theorem localFieldEquiv_algebraMap (x : ℤ_[q]) :
    localFieldEquiv q (algebraMap ℤ_[q] (dvr q).K x) = algebraMap ℤ_[q] ℚ_[q] x :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl ℤ_[q]) x

theorem coefficientField_square :
    (localFieldEquiv q).toRingHom.comp (dvr q).coefficientInclusion =
      (Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Crystalline.CoefficientAdapter.Witt q)
  intro w
  change localFieldEquiv q ((dvr q).coefficientInclusion
    (algebraMap (Crystalline.CoefficientAdapter.Witt q) (dvr q).K₀ w)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.coefficientInclusion_algebraMap,
    localFieldEquiv_algebraMap]
  exact (Crystalline.CoefficientAdapter.coefficientFieldEquiv_algebraMap q w).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DVR.PadicBase
