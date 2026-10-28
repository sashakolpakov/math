import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ResidueBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.CartierIntersection

/-! # Proper Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProperReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual residue reciprocity for a proper pair on a normal local surface

Every codimension-one point sees at least one equation as a unit, by the
proved minimal-prime criterion and the proper-parameter hypothesis.
The full residue boundary is therefore the actual Cartier intersection
difference, which vanishes by the checked geometric surface symmetry.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

local instance affineProperReciprocity_stalkAlgebra (x : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x

def affineFunctionUnit (a : R) (ha : a ≠ 0) : (Spec (CommRingCat.of R)).functionFieldˣ :=
  Units.mk0 (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R a))
    (RegularDivisor.BundleCycles.globalFunctionFieldElement_ne_zero (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R a)
      ((map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).injective).mpr ha))

omit [IsNoetherianRing R] in
theorem affineNormal_stalk_integrallyClosed [IsIntegrallyClosed R] (x : Spec (CommRingCat.of R)) :
    IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  let : x.asIdeal.IsPrime := (show PrimeSpectrum R from x).isPrime
  let : IsLocalization x.asIdeal.primeCompl ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
    StructureSheaf.IsLocalization.to_stalk R (show PrimeSpectrum R from x)
  exact isIntegrallyClosed_of_isLocalization ((Spec (CommRingCat.of R)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

omit [IsDomain R] [IsNoetherianRing R] in
theorem affineRegularGerm_isUnit (a : R) (x : Spec (CommRingCat.of R)) (ha : a ∉ x.asIdeal) :
    IsUnit ((Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (Divisor.BundleCycles.affineAmbientSection R a)) := by
  have hu : x ∈ (Spec (CommRingCat.of R)).basicOpen (Divisor.BundleCycles.affineAmbientSection R a) := by
    unfold Divisor.BundleCycles.affineAmbientSection
    rw [basicOpen_eq_of_affine]
    exact ha
  exact (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R a) x (by trivial)).mp hu

variable [IsLocalRing R]

theorem affineProperPair_unit_at_divisor (a b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (x : Spec (CommRingCat.of R)) (hx : coheight x = 1) :
    IsUnit ((Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (Divisor.BundleCycles.affineAmbientSection R a)) ∨
      IsUnit ((Spec (CommRingCat.of R)).presheaf.germ ⊤ x (by trivial) (Divisor.BundleCycles.affineAmbientSection R b)) := by
  by_cases hbP : b ∈ x.asIdeal
  · exact Or.inl (affineRegularGerm_isUnit R a x
      (SurfaceParameters.BundleCycles.surfaceParameter_not_mem_minimal a b hdim hab x.asIdeal (Divisor.BundleCycles.affineDivisorPoint_mem_minimal b hb x hx hbP)))
  · exact Or.inr (affineRegularGerm_isUnit R b x hbP)

theorem affineProperResidueBoundary_zero [IsIntegrallyClosed R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (affineNormal_stalk_integrallyClosed R)
      (affineFunctionUnit R a ha) (affineFunctionUnit R b hb) = 0 := by
  rw [Proper.ResidueBoundary.BundleCycles.normalResidueBoundaryCycle_proper (Spec (CommRingCat.of R)) (affineNormal_stalk_integrallyClosed R)
    (Divisor.BundleCycles.affineAmbientSection R a) (Divisor.BundleCycles.affineAmbientSection R b)
    (affineProperPair_unit_at_divisor R a b hb hdim hab)
    (affineFunctionUnit R a ha) (affineFunctionUnit R b hb) rfl rfl]
  exact sub_eq_zero.mpr (CartierIntersection.BundleCycles.affinePrincipalCartier_intersections_comm a b ha hb hdim hab)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProperReciprocity.BundleCycles
