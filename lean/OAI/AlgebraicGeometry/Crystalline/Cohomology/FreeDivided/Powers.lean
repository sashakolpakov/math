import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientPowers
import Mathlib.RingTheory.Localization.FractionRing

/-! # Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers

noncomputable section

/-!
# Augmentation divided powers over every commutative ring

Every coefficient ring is a quotient of its polynomial presentation over
the integers. That presentation embeds in its characteristic-zero fraction
field. The proved coefficient-quotient construction therefore supplies
divided powers on the actual free divided-power algebra over any ring,
with the expected operations on coordinate divided powers.
-/

universe u

variable (R : Type u) [CommRing R]

def Source := MvPolynomial R ℤ

instance sourceCommRing : CommRing (Source R) := inferInstanceAs (CommRing (MvPolynomial R ℤ))
instance sourceDomain : IsDomain (Source R) := inferInstanceAs (IsDomain (MvPolynomial R ℤ))
instance sourceCharZero : CharZero (Source R) := inferInstanceAs (CharZero (MvPolynomial R ℤ))

def reduction : Source R →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) id

instance sourceAlgebra : Algebra (Source R) R := (reduction R).toAlgebra

theorem reduction_surjective : Function.Surjective (algebraMap (Source R) R) := by
  intro r
  exact ⟨MvPolynomial.X r, MvPolynomial.eval₂Hom_X' _ _ _⟩

omit [CommRing R] in
theorem fraction_injective : Function.Injective (algebraMap (Source R) (FractionRing (Source R))) :=
  IsFractionRing.injective (Source R) (FractionRing (Source R))

variable (σ : Type u)

/-- Divided powers on the exact augmentation kernel of the actual free algebra. -/
def dividedPowers : DividedPowers
    (RingHom.ker (Multivariable.Reduction.MultivariableReduction.augmentation R σ).toRingHom) :=
  Divided.AlgebraQuotientPowers.DividedAlgebraQuotientPowers.dividedPowers (Source R) R σ (FractionRing (Source R))
    (fraction_injective R) (reduction_surjective R)

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (dividedPowers R σ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) =
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i :=
  Divided.AlgebraQuotientPowers.DividedAlgebraQuotientPowers.coordinate_dpow (Source R) R σ (FractionRing (Source R))
    (fraction_injective R) (reduction_surjective R) n i

theorem generator_dpow (n m : ℕ) (i : σ) :
    (dividedPowers R σ).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (m + 1) i) =
      (Nat.uniformBell n (m + 1) : R) •
        Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ (n * (m + 1)) i := by
  rw [← coordinate_dpow R σ (m + 1) i,
    (dividedPowers R σ).dpow_comp (Nat.succ_ne_zero m)
      (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem R σ i), coordinate_dpow]
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeDivided.Powers.FreeDividedPowers
