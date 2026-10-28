import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence

/-! # Algebra Quotient Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientPowers.DividedAlgebraQuotientPowers

noncomputable section

/-!
# Augmentation divided powers after surjective coefficient change

The quotient equivalence respects the actual augmentations. Transporting
the constructed quotient divided powers therefore equips the exact
augmentation kernel of the free algebra over the new coefficient ring.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (S R σ K : Type u) [CommRing S] [CommRing R] [Algebra S R]
  [Field K] [CharZero K] [Algebra S K]
  (h : Function.Injective (algebraMap S K))
  (hs : Function.Surjective (algebraMap S R))

local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "L" => RingHom.ker (algebraMap S R)
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.Ring S R σ hs
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotient S R σ hs
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotientIdeal S R σ hs
local notation "δQ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotientPowers S R σ K h hs
local notation "eΓ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.algebraEquiv S R σ K h hs
local notation "εS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation S σ
local notation "εR" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ

def reduction : Q →+* R :=
  (AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.coefficientEquiv S R hs).toRingHom.comp
    (AugmentationCoefficient.AugmentationCoefficientQuotient.reduction S GS L εS).toRingHom

theorem reduction_quotient (a : GS) : reduction S R σ hs (q a) = algebraMap S R (εS a) := rfl

theorem reduction_kernel : RingHom.ker (reduction S R σ hs) = J :=
  (RingHom.ker_comp_of_injective
    (AugmentationCoefficient.AugmentationCoefficientQuotient.reduction S GS L εS).toRingHom
    (AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.coefficientEquiv S R hs).injective).trans
      (AugmentationCoefficient.AugmentationCoefficientQuotient.reduction_kernel S GS L εS)

theorem augmentation_square : (εR).toRingHom.comp (eΓ).symm.toRingHom = reduction S R σ hs := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change εR (AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.toTarget S R σ hs (q a)) = reduction S R σ hs (q a)
  rw [AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.toTarget_quotient,
    AlgebraBaseChange.DividedAlgebraBaseChange.augmentation_map, reduction_quotient]

theorem ideal_map : (J).map (eΓ).symm.toRingHom = RingHom.ker (εR).toRingHom := by
  rw [← reduction_kernel S R σ hs, ← augmentation_square S R σ K h hs]
  change (Ideal.comap (eΓ).symm.toRingHom (RingHom.ker (εR).toRingHom)).map (eΓ).symm.toRingHom = _
  exact Ideal.map_comap_of_surjective _ (eΓ).symm.surjective _

/-- The actual free divided-power algebra over R, with its augmentation PD structure. -/
def dividedPowers : DividedPowers (RingHom.ker (εR).toRingHom) :=
  DividedPowers.ofRingEquiv (e := (eΓ).symm.toRingEquiv) (ideal_map S R σ K h hs) δQ

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (dividedPowers S R σ K h hs).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i := by
  change (eΓ).symm ((δQ).dpow n ((eΓ) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1 i))) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i
  have hgen (m : ℕ) : (eΓ) (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ m i) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ m i) :=
    AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.fromTarget_generator S R σ K h hs m i
  rw [hgen]
  have hd : (δQ).dpow n (q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ n i) :=
    AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.coordinate_dpow S R σ K h hs n i
  rw [hd, ← hgen]
  exact (eΓ).symm_apply_apply _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientPowers.DividedAlgebraQuotientPowers
