import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraBaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.AugmentationPowers

/-! # Algebra Quotient Equivalence -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence

noncomputable section

/-!
# The free divided-power algebra under a surjective coefficient change

A coefficient quotient of a characteristic-zero free PD algebra carries
the augmentation divided powers constructed earlier. Their weak universal
property identifies the quotient with the actual free divided-power
algebra over the quotient coefficient ring, even when that ring has torsion.
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
def Ring (_hs : Function.Surjective (algebraMap S R)) :=
  AugmentationCoefficient.AugmentationCoefficientQuotient.Ring S GS L

instance ringCommRing : CommRing (Ring S R σ hs) :=
  inferInstanceAs (CommRing (AugmentationCoefficient.AugmentationCoefficientQuotient.Ring S GS L))

instance ringSourceAlgebra : Algebra S (Ring S R σ hs) :=
  inferInstanceAs (Algebra S (AugmentationCoefficient.AugmentationCoefficientQuotient.Ring S GS L))

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.Ring S R σ hs
def quotient : GS →ₐ[S] Q := AugmentationCoefficient.AugmentationCoefficientQuotient.quotient S GS L

def quotientIdeal : Ideal Q :=
  AugmentationCoefficient.AugmentationCoefficientQuotient.ideal S GS L (Multivariable.Reduction.MultivariableReduction.augmentation S σ)

def quotientPowers : DividedPowers (quotientIdeal S R σ hs) :=
  Multivariable.AugmentationPowers.MultivariableAugmentationPowers.quotientPowers S σ K h L

local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotient S R σ hs
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotientIdeal S R σ hs
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence.quotientPowers S R σ K h hs

def coefficientEquiv : (S ⧸ L) ≃ₐ[S] R :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S R) hs

def coefficients : R →ₐ[S] Q :=
  (AugmentationCoefficient.AugmentationCoefficientQuotient.constants S GS L).comp (coefficientEquiv S R hs).symm.toAlgHom

theorem coefficients_algebraMap (s : S) : coefficients S R σ hs (algebraMap S R s) = q (algebraMap S GS s) :=
  (coefficients S R σ hs).commutes s

instance targetAlgebra : Algebra R Q := (coefficients S R σ hs).toRingHom.toAlgebra

instance targetTower : IsScalarTower S R Q :=
  IsScalarTower.of_algebraMap_eq' (coefficients S R σ hs).comp_algebraMap.symm

def toTarget : Q →ₐ[S] GR :=
  Ideal.Quotient.liftₐ ((L).map (algebraMap S GS)) (AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ)
    (fun _ ha => AlgebraBaseChange.DividedAlgebraBaseChange.coefficientIdeal_le_kernel S R σ L le_rfl ha)

theorem toTarget_quotient (a : GS) : toTarget S R σ hs (q a) = AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ a := rfl

def toTargetOverR : Q →ₐ[R] GR where
  __ := (toTarget S R σ hs).toRingHom
  commutes' a := by
    obtain ⟨s, rfl⟩ := hs a
    change toTarget S R σ hs (coefficients S R σ hs (algebraMap S R s)) = _
    rw [coefficients_algebraMap, toTarget_quotient, AlgebraBaseChange.DividedAlgebraBaseChange.map_coefficient]

def coordinate (i : σ) : Q := q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)

theorem coordinate_mem (i : σ) : coordinate S R σ hs i ∈ J :=
  Ideal.mem_map_of_mem _ (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem S σ i)

theorem coordinate_dpow (n : ℕ) (i : σ) :
    (δ).dpow n (coordinate S R σ hs i) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ n i) := by
  have hd : (δ).dpow n (q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) =
      q ((Multivariable.AugmentationPowers.MultivariableAugmentationPowers.dividedPowers S σ K h).dpow n (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) :=
    (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.quotient_isDPMorphism S σ K h L).dpow_comp
      (n := n) _ (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_mem S σ i)
  exact hd.trans (congrArg q (Multivariable.AugmentationPowers.MultivariableAugmentationPowers.coordinate_dpow S σ K h n i))

def fromTarget : GR →ₐ[R] Q :=
  DividedPowerAlgebra.lift δ (Finsupp.linearCombination R (coordinate S R σ hs)) (by
    intro a
    classical
    change (∑ i ∈ a.support, a i • coordinate S R σ hs i) ∈ J
    apply Submodule.sum_mem
    intro i _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (coordinate_mem S R σ hs i))

theorem fromTarget_generator (n : ℕ) (i : σ) :
    fromTarget S R σ K h hs (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ n i) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ n i) := by
  change DividedPowerAlgebra.lift _ _ _ (DividedPowerAlgebra.dp R n (Finsupp.single i (1 : R))) = _
  rw [DividedPowerAlgebra.lift_apply_dp, Finsupp.linearCombination_single, one_smul]
  change (δ).dpow n (q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ 1 i)) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator S σ n i)
  exact coordinate_dpow S R σ K h hs n i

theorem fromTarget_monomial (d : σ →₀ ℕ) :
    fromTarget S R σ K h hs (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial S σ d) := by
  classical
  simp only [Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial, Finsupp.prod, map_prod, fromTarget_generator]

theorem toTarget_fromTarget :
    (toTargetOverR S R σ hs).comp (fromTarget S R σ K h hs) = AlgHom.id R GR := by
  have he : ((toTargetOverR S R σ hs).comp (fromTarget S R σ K h hs)).toLinearMap =
      (AlgHom.id R GR).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top R σ)
    rintro _ ⟨d, rfl⟩
    change toTarget S R σ hs (fromTarget S R σ K h hs (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d)) = Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial R σ d
    rw [fromTarget_monomial, toTarget_quotient, AlgebraBaseChange.DividedAlgebraBaseChange.map_monomial]
  exact AlgHom.ext (LinearMap.congr_fun he)

theorem fromTarget_toTarget :
    (fromTarget S R σ K h hs).comp (toTargetOverR S R σ hs) = AlgHom.id R Q := by
  have he : (((fromTarget S R σ K h hs).restrictScalars S).comp (AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ)).toLinearMap =
      (q).toLinearMap := by
    apply LinearMap.ext_on (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.span_monomial_eq_top S σ)
    rintro _ ⟨d, rfl⟩
    change fromTarget S R σ K h hs (AlgebraBaseChange.DividedAlgebraBaseChange.map S R σ (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial S σ d)) = q (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.monomial S σ d)
    rw [AlgebraBaseChange.DividedAlgebraBaseChange.map_monomial, fromTarget_monomial]
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact LinearMap.congr_fun he a

/-- The coefficient quotient is the actual free divided-power algebra over R. -/
def algebraEquiv : GR ≃ₐ[R] Q :=
  AlgEquiv.ofAlgHom (fromTarget S R σ K h hs) (toTargetOverR S R σ hs)
    (fromTarget_toTarget S R σ K h hs) (toTarget_fromTarget S R σ K h hs)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AlgebraQuotientEquivalence.DividedAlgebraQuotientEquivalence
