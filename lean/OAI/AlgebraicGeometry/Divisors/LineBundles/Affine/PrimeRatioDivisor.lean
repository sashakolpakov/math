import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalQuotients
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProperReciprocity

/-! # Prime Ratio Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeRatioDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete divisors of actual restricted affine ratios
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (R : Type) [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem affineSupportRegularFunction_ne_zero (P : Ideal R) [P.IsPrime] (a : R) (ha : a ∉ P) :
    Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R a) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P)) ≠ 0 :=
  Support.PrincipalQuotients.BundleCycles.supportRegularFunction_ne_zero_of_unit_germ (PrimeSupport.BundleCycles.affinePrimePoint R P) (Divisor.BundleCycles.affineAmbientSection R a)
    (ProperReciprocity.BundleCycles.affineRegularGerm_isUnit R a (PrimeSupport.BundleCycles.affinePrimePoint R P) ha).unit
    (ProperReciprocity.BundleCycles.affineRegularGerm_isUnit R a (PrimeSupport.BundleCycles.affinePrimePoint R P) ha).unit_spec

variable [IsNoetherianRing R] [IsLocalRing R]

theorem affinePrimeSupportRatio_divisor (a c r : R) (hr : r ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {r}).minimalPrimes) (ha : a ∉ P) (hc : c ∉ P) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P))
      (Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R a) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P)) /
        Principal.CartierCycle.BundleCycles.supportRegularFunction (Divisor.BundleCycles.affineAmbientSection R c) (irreducibleSetEquivPoints.symm (PrimeSupport.BundleCycles.affinePrimePoint R P))) =
      Finsupp.single (LocalDivisor.BundleCycles.affineLocalClosedPoint R)
        ((PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P : ℚ) - (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength c P : ℚ)) := by
  have he := SurfaceGeometricIntersection.BundleCycles.surfacePrimeRationalCycle_eq_length_difference a c r hr hdim P hP ha hc
  unfold SurfaceGeometricIntersection.BundleCycles.surfacePrimeRationalCycle at he
  rw [Divisor.BundleCycles.affinePrimeLocalFunction_ratio R P a c, PrimeSupport.BundleCycles.affinePrime_imageClosure R P] at he
  exact he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeRatioDivisor.BundleCycles
