import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Universal
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Characteristic Zero Presentation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation

noncomputable section

/-!
# Characteristic-zero presentations of arbitrary PD rings

First present the coefficient ring by a polynomial ring over the integers.
The free divided-power algebra on the elements of the target PD ideal
then maps surjectively to the target ring and onto its PD ideal. Its
polynomial realization makes the source an integral domain of
characteristic zero. This constructs a PD presentation even for torsion
target rings; no lifting assumption is imposed on them.
-/

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "Z" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers.Source R

def Ring (_δ : DividedPowers I) := DividedPowerAlgebra Z (I →₀ Z)

instance ringCommRing : CommRing (PDCharacteristicZeroPresentation.Ring R I δ) :=
  inferInstanceAs (CommRing (DividedPowerAlgebra Z (I →₀ Z)))

instance coefficientAlgebra : Algebra Z (PDCharacteristicZeroPresentation.Ring R I δ) :=
  inferInstanceAs (Algebra Z (DividedPowerAlgebra Z (I →₀ Z)))

local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.Ring R I δ

def realize : S →ₐ[Z] MvPolynomial I (FractionRing Z) :=
  Multivariable.DividedAlgebra.MultivariableDividedAlgebra.realize Z I (FractionRing Z)

theorem realize_injective : Function.Injective (realize R I δ) :=
  Multivariable.DividedAlgebra.MultivariableDividedAlgebra.realize_injective Z I (FractionRing Z)
    (FreeDivided.Powers.FreeDividedPowers.fraction_injective R)

instance ringDomain : IsDomain S := (realize_injective R I δ).isDomain (realize R I δ)

instance ringCharZero : CharZero S where
  cast_injective := by
    intro m n hmn
    apply Nat.cast_injective (R := MvPolynomial I (FractionRing Z))
    simpa only [map_natCast] using congrArg (realize R I δ) hmn

def ideal : Ideal S := RingHom.ker (Multivariable.Reduction.MultivariableReduction.augmentation Z I).toRingHom

def dividedPowers : DividedPowers (ideal R I δ) := FreeDivided.Powers.FreeDividedPowers.dividedPowers Z I

def reduction : S →ₐ[Z] R :=
  FreeDivided.Universal.FreeDividedUniversal.lift Z I R I δ Subtype.val Subtype.property

instance targetAlgebra : Algebra S R := (reduction R I δ).toRingHom.toAlgebra

instance targetTower : IsScalarTower Z S R :=
  IsScalarTower.of_algebraMap_eq' (reduction R I δ).comp_algebraMap.symm

def coordinate (a : I) : S := Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Z I 1 a

theorem coordinate_mem (a : I) : coordinate R I δ a ∈ ideal R I δ :=
  Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem Z I a

theorem reduction_coordinate (a : I) : reduction R I δ (coordinate R I δ a) = a :=
  FreeDivided.Universal.FreeDividedUniversal.lift_coordinate Z I R I δ Subtype.val Subtype.property a

/-- The actual source divided powers descend to the given target divided powers. -/
theorem reduction_isDPMorphism :
    DividedPowers.IsDPMorphism (dividedPowers R I δ) δ (algebraMap S R) :=
  FreeDivided.Universal.FreeDividedUniversal.lift_isDPMorphism Z I R I δ Subtype.val Subtype.property

theorem reduction_surjective : Function.Surjective (algebraMap S R) := by
  intro a
  obtain ⟨z, rfl⟩ := FreeDivided.Powers.FreeDividedPowers.reduction_surjective R a
  exact ⟨algebraMap Z S z, (reduction R I δ).commutes z⟩

theorem ideal_map : (ideal R I δ).map (algebraMap S R) = I := by
  apply le_antisymm (reduction_isDPMorphism R I δ).ideal_comp
  intro a ha
  have hm := Ideal.mem_map_of_mem (algebraMap S R) (coordinate_mem R I δ ⟨a, ha⟩)
  change reduction R I δ (coordinate R I δ ⟨a, ha⟩) ∈ _ at hm
  rw [reduction_coordinate] at hm
  exact hm

theorem fraction_injective : Function.Injective (algebraMap S (FractionRing S)) :=
  IsFractionRing.injective S (FractionRing S)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation
