import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.GeneralPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationCoefficient

/-! # Augmentation Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.AugmentationPowers.MultivariableAugmentationPowers

noncomputable section

/-!
# Augmentation divided powers and arbitrary coefficient quotients

The actual free divided-power algebra over an embedded characteristic-zero
ring has divided powers on its exact augmentation kernel. These descend
modulo every coefficient ideal, including quotients with torsion.
-/

universe u

variable (R σ : Type u) [CommRing R]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ (⊥ : Ideal R)

theorem augmentation_kernel : RingHom.ker (ε).toRingHom = IG := by
  rw [← Reduction.MultivariableReduction.reduction_kernel R σ (⊥ : Ideal R)]
  apply Ideal.ext
  intro a
  change ε a = 0 ↔ Ideal.Quotient.mk (⊥ : Ideal R) (ε a) = 0
  constructor
  · intro ha
    rw [ha, map_zero]
  · intro ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha

variable (K : Type u) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))

/-- Divided powers on the actual kernel of the augmentation. -/
def dividedPowers : DividedPowers (RingHom.ker (ε).toRingHom) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl G)
    (by
      change (IG).map (RingHom.id G) = RingHom.ker (ε).toRingHom
      rw [Ideal.map_id]
      exact (augmentation_kernel R σ).symm)
    (GeneralPowers.MultivariableGeneralPowers.dividedPowers R σ K h ⊥ (dividedPowersBot R))

theorem coordinate_mem (i : σ) : DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i ∈
    RingHom.ker (ε).toRingHom := by
  rw [augmentation_kernel]
  exact Multivariable.DividedPowers.MultivariableDividedPowers.positive_generator_mem R σ ⊥ i 1 one_ne_zero

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (dividedPowers R σ K h).dpow n (DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
      DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i :=
  GeneralPowers.MultivariableGeneralPowers.coordinate_dpow R σ K h ⊥ (dividedPowersBot R) n i

variable (L : Ideal R)

def quotientPowers : DividedPowers (AugmentationCoefficient.AugmentationCoefficientQuotient.ideal R G L ε) :=
  AugmentationCoefficient.AugmentationCoefficientQuotient.dividedPowers R G L ε (dividedPowers R σ K h)

theorem quotient_isDPMorphism : DividedPowers.IsDPMorphism (dividedPowers R σ K h)
    (quotientPowers R σ K h L) (AugmentationCoefficient.AugmentationCoefficientQuotient.quotient R G L).toRingHom :=
  AugmentationCoefficient.AugmentationCoefficientQuotient.quotient_isDPMorphism R G L ε (dividedPowers R σ K h)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.AugmentationPowers.MultivariableAugmentationPowers
