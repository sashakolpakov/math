import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.RelativeDivided

/-! # Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers

noncomputable section

/-!
# Relative free divided powers over arbitrary PD bases

The constructed characteristic-zero PD presentation and the proved
coefficient descent equip the actual free divided-power algebra with
the full relative PD ideal. The structure extends the given base divided
powers and has the native divided coordinate operations, even when the
base ring has torsion.
-/

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.Ring R I δ
local notation "IS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.ideal R I δ
local notation "δS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.dividedPowers R I δ
local notation "h" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.fraction_injective R I δ
local notation "hs" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.reduction_surjective R I δ
local notation "hφ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.reduction_isDPMorphism R I δ
local notation "hI" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CharacteristicZeroPresentation.PDCharacteristicZeroPresentation.ideal_map R I δ
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I

/-- The full relative PD structure on the actual free algebra over any PD ring. -/
def dividedPowers : DividedPowers J :=
  RelativeDivided.RelativeDividedQuotient.dividedPowers S R σ (FractionRing S) h hs IS δS I δ hφ hI

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δ (dividedPowers R σ I δ) (algebraMap R G) :=
  RelativeDivided.RelativeDividedQuotient.base_isDPMorphism S R σ (FractionRing S) h hs IS δS I δ hφ hI

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (dividedPowers R σ I δ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i :=
  RelativeDivided.RelativeDividedQuotient.coordinate_dpow S R σ (FractionRing S) h hs IS δS I δ hφ hI n i

theorem generator_dpow (n m : ℕ) (i : σ) :
    (dividedPowers R σ I δ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i) =
      (Nat.uniformBell n (m + 1) : R) •
        Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n * (m + 1)) i := by
  rw [← coordinate_dpow R σ I δ (m + 1) i,
    (dividedPowers R σ I δ).dpow_comp (Nat.succ_ne_zero m)
      (Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ I i 1 one_ne_zero), coordinate_dpow]
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers
