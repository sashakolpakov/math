import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.BranchPushforward

/-! # Norm Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the complete finite affine divisor pushes to the order of its norm
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory IsDedekindDomain
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

attribute [local instance] FractionRing.liftAlgebra

variable (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDiscreteValuationRing R]
    [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]
    [Module.IsTorsionFree R S] [PerfectField (FractionRing R)]

theorem affineNormPrincipalDivisor_pushforward (g : FractionRing S) (hg : g ≠ 0) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of S)) (Normal.AffineOrder.BundleCycles.normalAffineFieldIso S g)) =
        Finsupp.single (IsLocalRing.closedPoint R : Spec (CommRingCat.of R))
          ((WithZero.log (Ring.ordFrac R (Algebra.norm (FractionRing R) g)) : ℤ) : ℚ) := by
  let : Finite (HeightOneSpectrum S) := IntersectionTheory.ProjectionFormula.BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  rw [Normal.BranchPushforward.BundleCycles.normalPrincipalPointDivisor_pushforward,
    IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm.log_ordFrac_norm R g hg]
  congr 1
  simp only [Normal.AffineOrder.BundleCycles.schemeOrder_eq_normalBranchOrder, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.NormDivisor.BundleCycles
