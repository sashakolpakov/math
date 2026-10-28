import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability

/-! # Coefficient Flatness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientFlatness

noncomputable section

/-!
# IntegralComparison: flatness of the actual lifted Witt coefficients

Witt vectors over a perfect field have characteristic zero and no
torsion over the integers. Flatness over the integers, and over the
lifted integer ring used at the IntegralComparison coefficient universe, follows.
-/

universe u

abbrev Integers := ULift.{u + 1} ℤ

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

abbrev Coeff := ULift.{u + 1} (WittVector p k)

theorem witt_flat : Module.Flat ℤ (WittVector p k) := by infer_instance

instance coefficientAlgebra : Algebra Integers.{u} (Coeff p k) :=
  ((ULift.ringEquiv : Coeff p k ≃+* WittVector p k).symm.toRingHom.comp
    ((Int.castRingHom (WittVector p k)).comp
      (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toRingHom)).toAlgebra

theorem lifted_flat : Module.Flat Integers.{u} (Coeff p k) := by
  rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]
  exact witt_flat p k

theorem coefficientMap_flat : (algebraMap Integers.{u} (Coeff p k)).Flat := by
  have hi : (Int.castRingHom (WittVector p k)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (witt_flat p k)
  exact ((RingHom.Flat.of_bijective (ULift.ringEquiv : Integers.{u} ≃+* ℤ).bijective).comp hi).comp
    (RingHom.Flat.of_bijective (ULift.ringEquiv : Coeff p k ≃+* WittVector p k).symm.bijective)

theorem coefficient_algebra_flat :
    letI : Module Integers.{u} (Coeff p k) := (coefficientAlgebra p k).toModule
    Module.Flat Integers.{u} (Coeff p k) := by
  let : Module Integers.{u} (Coeff p k) := (coefficientAlgebra p k).toModule
  exact RingHom.flat_algebraMap_iff.mp (coefficientMap_flat p k)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientFlatness
