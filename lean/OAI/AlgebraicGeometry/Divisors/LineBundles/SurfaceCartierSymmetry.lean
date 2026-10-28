import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceGeometricIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection

/-! # Surface Cartier Symmetry -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceCartierSymmetry.BundleCycles

noncomputable section

/-!
# LineBundleCycles: symmetry of actual proper Cartier intersections on a local surface

The cycles restrict the ambient equations to the actual prime supports,
take their geometric principal divisors, and use the existing local
equation multiplicities. The two complete cycles agree by the proved
local length symmetry, including for singular integral surfaces.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped Classical

variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem surfacePrimeRationalCycle_regular (a : R) (P : Ideal R) [P.IsPrime] :
    SurfaceGeometricIntersection.BundleCycles.surfacePrimeRationalCycle a 1 P =
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Affine.Divisor.BundleCycles.affineAmbientSection R a) (CycleClass.Geometric.StratumClosure.integralImageClosure (Affine.PrimeSupport.BundleCycles.affinePrimeQuotientMap R P)) := by
  have h1 : Principal.CartierCycle.BundleCycles.supportRegularFunction (Affine.Divisor.BundleCycles.affineAmbientSection R 1)
      (CycleClass.Geometric.StratumClosure.integralImageClosure (Affine.PrimeSupport.BundleCycles.affinePrimeQuotientMap R P)) = 1 := by
    unfold Principal.CartierCycle.BundleCycles.supportRegularFunction Affine.Divisor.BundleCycles.affineAmbientSection RegularDivisor.BundleCycles.globalFunctionFieldElement
    rw [map_one, map_one, map_one]
  unfold SurfaceGeometricIntersection.BundleCycles.surfacePrimeRationalCycle
  rw [Affine.Divisor.BundleCycles.affinePrimeLocalFunction_ratio, h1, div_one]
  rfl

def surfaceCartierSummand (a b : R) (P : Ideal R) : Spec (CommRingCat.of R) →₀ ℚ :=
  if hP : P ∈ (Ideal.span {b}).minimalPrimes then
    letI : P.IsPrime := hP.isPrime
    (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP.isPrime : ℚ) •
      Principal.CartierCycle.BundleCycles.principalCartierPointCycle (Affine.Divisor.BundleCycles.affineAmbientSection R a) (CycleClass.Geometric.StratumClosure.integralImageClosure (Affine.PrimeSupport.BundleCycles.affinePrimeQuotientMap R P))
  else 0

def surfaceCartierIntersection (a b : R) : Spec (CommRingCat.of R) →₀ ℚ :=
  ∑ P ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset,
    surfaceCartierSummand a b P

theorem surfaceCartierSummand_eq_rational (a b : R) (P : Ideal R) :
    surfaceCartierSummand a b P = SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalSummand a 1 b P := by
  by_cases hP : P ∈ (Ideal.span {b}).minimalPrimes
  · rw [surfaceCartierSummand, dite_eq_left hP, SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalSummand, dite_eq_left hP,
      surfacePrimeRationalCycle_regular]
  · rw [surfaceCartierSummand, dite_eq_right hP, SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalSummand, dite_eq_right hP]

theorem surfaceCartierIntersection_eq_rational (a b : R) :
    surfaceCartierIntersection a b = SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalIntersection a 1 b := by
  unfold surfaceCartierIntersection SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalIntersection
  exact Finset.sum_congr rfl (fun P _ => surfaceCartierSummand_eq_rational a b P)

variable [IsDomain R] [IsLocalRing R]

theorem surfaceCartierIntersection_eq_single (a b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceCartierIntersection a b =
      Finsupp.single (Affine.LocalDivisor.BundleCycles.affineLocalClosedPoint R) (SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber a b : ℚ) := by
  rw [surfaceCartierIntersection_eq_rational,
    SurfaceGeometricIntersection.BundleCycles.surfaceGeometricRationalIntersection_eq_single a 1 b hb hdim,
    SurfaceRationalOrderIntersection.BundleCycles.surfaceRationalIntersectionNumber_one_denominator a b hb hdim hab]

theorem surfaceCartierIntersection_comm (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceCartierIntersection a b = surfaceCartierIntersection b a := by
  have hba : (Ideal.span {b, a}).radical = IsLocalRing.maximalIdeal R :=
    (congrArg (fun s : Set R => (Ideal.span s).radical) (Set.pair_comm b a)).trans hab
  rw [surfaceCartierIntersection_eq_single a b hb hdim hab,
    surfaceCartierIntersection_eq_single b a ha hdim hba,
    SurfaceRationalOrderIntersection.BundleCycles.surfaceIntersectionNumber_comm a b ha hb hdim hab]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceCartierSymmetry.BundleCycles
