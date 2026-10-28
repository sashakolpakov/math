import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.LocalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeCurve

/-! # Surface Geometric Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceGeometricIntersection.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: actual geometric prime-support divisors recover the local surface orders

The rational function is the actual quotient of a and c in R/P, carried
through the canonical quotient-spectrum and reduced-image isomorphisms.
Its geometric principal cycle has the previously computed rational order
as coefficient at the original local surface's closed point.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R : Type} [CommRing R] [IsNoetherianRing R]

def surfacePrimeRationalCycle (a c : R) (P : Ideal R) [P.IsPrime] : Spec (CommRingCat.of R) →₀ ℚ :=
  Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure (Affine.PrimeSupport.BundleCycles.affinePrimeQuotientMap R P))
    (Affine.LocalDivisor.BundleCycles.affinePrimeLocalFunction R P (SurfaceRationalOrderIntersection.BundleCycles.primeSupportRationalFunction a c P))

variable [IsDomain R] [IsLocalRing R]

theorem surfacePrimeRationalCycle_eq_single (a c b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) :
    letI : P.IsPrime := hP.isPrime
    surfacePrimeRationalCycle a c P =
      Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R) (SurfaceRationalOrderIntersection.BundleCycles.surfacePrimeRationalOrder a c b hb hdim P hP : ℚ) := by
  let : P.IsPrime := hP.isPrime
  exact Affine.LocalDivisor.BundleCycles.affinePrimeLocal_principalDivisor R P (SurfacePrimeCurve.BundleCycles.surfacePrimeQuotient_dimension b hb hdim P hP)
    (SurfaceRationalOrderIntersection.BundleCycles.primeSupportRationalFunction a c P)

theorem surfacePrimeRationalCycle_eq_length_difference (a c b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes)
    (ha : a ∉ P) (hc : c ∉ P) :
    letI : P.IsPrime := hP.isPrime
    surfacePrimeRationalCycle a c P = Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R)
      ((PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P : ℚ) - (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength c P : ℚ)) := by
  let : P.IsPrime := hP.isPrime
  rw [surfacePrimeRationalCycle_eq_single a c b hb hdim P hP,
    SurfaceRationalOrderIntersection.BundleCycles.surfacePrimeRationalOrder_eq_difference a c b hb hdim P hP ha hc,
    Int.cast_sub]

end

/-!
# LineBundleCycles: the local surface formula as an equality of actual geometric cycles

Sum the principal divisors on the actual prime quotient supports with
their local equation multiplicities. The entire geometric cycle equals
the computed rational intersection number at the closed point.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped Classical

variable {R : Type} [CommRing R] [IsNoetherianRing R]

def surfaceGeometricRationalSummand (a c b : R) (P : Ideal R) : Spec (CommRingCat.of R) →₀ ℚ :=
  if hP : P ∈ (Ideal.span {b}).minimalPrimes then
    letI : P.IsPrime := hP.isPrime
    (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP.isPrime : ℚ) • surfacePrimeRationalCycle a c P
  else 0

def surfaceGeometricRationalIntersection (a c b : R) : Spec (CommRingCat.of R) →₀ ℚ :=
  ∑ P ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset,
    surfaceGeometricRationalSummand a c b P

variable [IsDomain R] [IsLocalRing R]

theorem surfaceGeometricRationalSummand_eq_single (a c b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) :
    surfaceGeometricRationalSummand a c b P = Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R)
      (SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionSummand a c b hb hdim P : ℚ) := by
  by_cases hP : P ∈ (Ideal.span {b}).minimalPrimes
  · let : P.IsPrime := hP.isPrime
    rw [surfaceGeometricRationalSummand, dite_eq_left hP,
      surfacePrimeRationalCycle_eq_single a c b hb hdim P hP,
      Finsupp.smul_single, smul_eq_mul, SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionSummand, dite_eq_left hP,
      Int.cast_mul, Int.cast_natCast]
  · rw [surfaceGeometricRationalSummand, dite_eq_right hP,
      SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionSummand, dite_eq_right hP, Int.cast_zero, Finsupp.single_zero]

theorem surfaceGeometricRationalIntersection_eq_single (a c b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) :
    surfaceGeometricRationalIntersection a c b = Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R)
      (SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionNumber a c b hb hdim : ℚ) := by
  unfold surfaceGeometricRationalIntersection SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionNumber
  rw [Int.cast_sum, Finsupp.single_finsetSum]
  exact Finset.sum_congr rfl (fun P _ => surfaceGeometricRationalSummand_eq_single a c b hb hdim P)

theorem surfaceGeometricRationalIntersection_eq_difference (a c b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (hcb : (Ideal.span {c, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceGeometricRationalIntersection a c b = Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R)
      ((SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber a b : ℚ) - (SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber c b : ℚ)) := by
  rw [surfaceGeometricRationalIntersection_eq_single a c b hb hdim,
    SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionNumber_eq_sub a c b hb hdim hab hcb, Int.cast_sub]

theorem surfaceGeometricRationalIntersection_eq_opposite_difference
    (a c b : R) (ha : a ≠ 0) (hc : c ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (hcb : (Ideal.span {c, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceGeometricRationalIntersection a c b = Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R)
      ((SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber b a : ℚ) - (SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber b c : ℚ)) := by
  rw [surfaceGeometricRationalIntersection_eq_single a c b hb hdim,
    SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionNumber_eq_opposite_sub a c b hb hdim hab hcb ha hc, Int.cast_sub]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceGeometricIntersection.BundleCycles
