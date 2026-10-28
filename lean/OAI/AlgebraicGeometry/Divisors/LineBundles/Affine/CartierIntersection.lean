import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceCartierSymmetry

/-! # Cartier Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.CartierIntersection.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual Cartier operation on a native affine divisor

Apply the existing point-cycle Cartier map to the full native divisor
of an affine equation. Its finite expansion is exactly the geometric
prime-support intersection sum, so proper local surface intersections
commute as actual operations on the original divisor cycles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped Classical

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem affineCartierIntersection_eq_surfaceCycle (a b : R) (hb : b ≠ 0) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap (Divisor.BundleCycles.affineAmbientSection R a)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R))
        (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R b))) =
      SurfaceCartierSymmetry.BundleCycles.surfaceCartierIntersection a b := by
  rw [Divisor.BundleCycles.affineRegularDivisor_eq_prime_sum R b hb, map_sum]
  have he : SurfaceCartierSymmetry.BundleCycles.surfaceCartierIntersection a b =
      ∑ P : Divisor.BundleCycles.affineDivisorPrimeIndex R b, SurfaceCartierSymmetry.BundleCycles.surfaceCartierSummand a b P.val :=
    Finset.sum_subtype
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset
      (fun _ => (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).mem_toFinset)
      (SurfaceCartierSymmetry.BundleCycles.surfaceCartierSummand a b)
  rw [he]
  apply Finset.sum_congr rfl
  intro P _
  let : P.val.IsPrime := P.property.isPrime
  rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, SurfaceCartierSymmetry.BundleCycles.surfaceCartierSummand, dite_eq_left P.property]
  exact congrArg (fun W => (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P.val P.property.isPrime : ℚ) •
    Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Divisor.BundleCycles.affineAmbientSection R a) W) (PrimeSupport.BundleCycles.affinePrime_imageClosure R P.val).symm

variable [IsLocalRing R]

theorem affinePrincipalCartier_intersections_comm (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap (Divisor.BundleCycles.affineAmbientSection R a)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R))
        (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R b))) =
    Principal.CartierFiber.BundleCycles.principalCartierPointMap (Divisor.BundleCycles.affineAmbientSection R b)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R))
        (RegularDivisor.BundleCycles.globalFunctionFieldElement (Spec (CommRingCat.of R)) (Divisor.BundleCycles.affineAmbientSection R a))) := by
  rw [affineCartierIntersection_eq_surfaceCycle a b hb, affineCartierIntersection_eq_surfaceCycle b a ha]
  exact SurfaceCartierSymmetry.BundleCycles.surfaceCartierIntersection_comm a b ha hb hdim hab

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.CartierIntersection.BundleCycles
