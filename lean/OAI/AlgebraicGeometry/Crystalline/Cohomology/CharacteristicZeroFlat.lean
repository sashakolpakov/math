import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallInteger
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Stability

/-! # Characteristic Zero Flat -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CharacteristicZeroFlat.CharacteristicZeroSheafCoefficients

noncomputable section

/-! # Exact coefficient restriction for the characteristic-zero generic fiber -/

open _root_.CategoryTheory Limits

universe u

variable (k : Type u) [Field k] [CharZero k]

abbrev Integers : Type u := SmallInteger.SmallIntegerSheafCoefficients.Integers

instance integerAlgebra : Algebra Integers.{u} k :=
  ((Int.castRingHom k).comp (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toRingHom).toAlgebra

theorem integerMap_flat : (algebraMap Integers.{u} k).Flat := by
  have hf : (Int.castRingHom k).Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstanceAs (Module.Flat ℤ k))
  exact (RingHom.Flat.of_bijective (ULift.ringEquiv : Integers.{u} ≃+* ℤ).bijective).comp hf

instance integer_flat :
    letI : Module Integers.{u} k := (integerAlgebra k).toModule
    Module.Flat Integers.{u} k := by
  let : Module Integers.{u} k := (integerAlgebra k).toModule
  exact RingHom.flat_algebraMap_iff.mp (integerMap_flat k)

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{u} Integers.{u})] [HasSheafify J (ModuleCat.{u} k)]
  [HasSheafify J AddCommGrpCat.{u}]

abbrev restriction : Sheaf J (ModuleCat.{u} k) ⥤ Sheaf J (ModuleCat.{u} Integers.{u}) :=
  NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves.restriction Integers.{u} k J

abbrev forget : Sheaf J (ModuleCat.{u} k) ⥤ Sheaf J AddCommGrpCat.{u} :=
  restriction k J ⋙ SmallInteger.SmallIntegerSheafCoefficients.forget J

instance forget_preservesInjectives : (forget k J).PreservesInjectiveObjects := by infer_instance

instance forget_preservesFiniteLimits : PreservesFiniteLimits (forget k J) := by infer_instance

instance forget_preservesFiniteColimits : PreservesFiniteColimits (forget k J) := by infer_instance

instance forget_additive : (forget k J).Additive := by infer_instance

def underlyingIso : forget k J ≅ sheafCompose J (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}) :=
  Iso.refl _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CharacteristicZeroFlat.CharacteristicZeroSheafCoefficients
