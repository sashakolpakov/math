import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimePairReciprocity
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Factorial Rational Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FactorialRationalReciprocity.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: residue reciprocity for all regular pairs on a factorial local surface

Prime factorization and the actual affine multiplicative maps reduce
every pair of nonzero equations to the checked prime-pair and unit cases.
Shared divisor components are allowed. This factorial case does not
replace the still-required argument for arbitrary normal local surfaces.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [IsLocalRing R] [IsIntegrallyClosed R] [UniqueFactorizationMonoid R]

theorem affinePrime_regularResidueBoundary_zero (p : R) (hp : Prime p)
    (hdim : ringKrullDim R = 2) (b : R) (hb : b ≠ 0) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R p hp.ne_zero) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0 := by
  refine (UniqueFactorizationMonoid.induction_on_prime
    (P := fun b => ∀ hb : b ≠ 0,
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
        (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R p hp.ne_zero) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0) b ?_ ?_ ?_) hb
  · intro hzero
    exact False.elim (hzero rfl)
  · intro u hu hune
    rw [ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_swap, AffineFunctionUnits.BundleCycles.affineResidueBoundary_unit_left R u hu, neg_zero]
  · intro a q ha hq ih haq
    rw [AffineFunctionUnits.BundleCycles.affineFunctionUnit_mul R q a hq.ne_zero ha, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_right,
      PrimePairReciprocity.BundleCycles.affinePrimePairResidueBoundary_zero R p q hp hq hdim, ih ha, add_zero]

theorem affineFactorialRegularResidueBoundary_zero (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0 := by
  refine (UniqueFactorizationMonoid.induction_on_prime
    (P := fun a => ∀ ha : a ≠ 0,
      Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
        (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R b hb) = 0) a ?_ ?_ ?_) ha
  · intro hzero
    exact False.elim (hzero rfl)
  · intro u hu hune
    exact AffineFunctionUnits.BundleCycles.affineResidueBoundary_unit_left R u hu _
  · intro a p ha hp ih hpa
    rw [AffineFunctionUnits.BundleCycles.affineFunctionUnit_mul R p a hp.ne_zero ha, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_left,
      affinePrime_regularResidueBoundary_zero R p hp hdim b hb, ih ha, add_zero]

end

/-!
# LineBundleCycles: full rational residue reciprocity on a factorial local surface

Every nonzero native rational function has actual affine numerator and
denominator representatives. Bilinearity and the proved regular-pair
factorization argument therefore give zero for the complete residue
cycle, without any properness restriction and including all poles.
The factorial hypothesis is confined to this intermediate case.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R]

local instance factorialReciprocity_fieldAlgebra : Algebra R (Spec (.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (.of R)))).hom.toAlgebra

local instance factorialReciprocity_isFractionRing : IsFractionRing R (Spec (.of R)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

theorem affineFunctionUnit_exists_ratio (g : (Spec (CommRingCat.of R)).functionFieldˣ) :
    ∃ (a c : R) (ha : a ≠ 0) (hc : c ≠ 0), g = Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R a ha / Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R c hc := by
  obtain ⟨a, c, hc, he⟩ := IsFractionRing.div_surjective R (g : (Spec (CommRingCat.of R)).functionField)
  have hc' : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have ha : a ≠ 0 := by
    intro hz
    apply g.ne_zero
    rw [← he, hz, map_zero, zero_div]
  refine ⟨a, c, ha, hc', ?_⟩
  apply Units.ext
  rw [Units.val_div_eq_div_val]
  exact he.symm

variable [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R] [UniqueFactorizationMonoid R]

theorem affineFactorialResidueBoundary_zero (hdim : ringKrullDim R = 2)
    (g h : (Spec (CommRingCat.of R)).functionFieldˣ) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R) g h = 0 := by
  obtain ⟨a, c, ha, hc, hg⟩ := affineFunctionUnit_exists_ratio R g
  obtain ⟨b, d, hb, hd, hh⟩ := affineFunctionUnit_exists_ratio R h
  rw [hg, hh, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_left, Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    Geometric.Steinberg.BundleCycles.normalResidueBoundaryCycle_div_right,
    affineFactorialRegularResidueBoundary_zero R a b ha hb hdim,
    affineFactorialRegularResidueBoundary_zero R a d ha hd hdim,
    affineFactorialRegularResidueBoundary_zero R c b hc hb hdim,
    affineFactorialRegularResidueBoundary_zero R c d hc hd hdim]
  simp only [sub_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FactorialRationalReciprocity.BundleCycles
