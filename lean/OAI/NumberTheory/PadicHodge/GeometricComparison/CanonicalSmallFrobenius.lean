import OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsFrobeniusPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallPullback

/-! # Canonical Small Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallFrobenius.CrystallineAdapter

noncomputable section

/-! The native small crystalline Frobenius, with its proved prime-field pullback normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def canonicalSmallFrobenius (p : ℕ) [Fact p.Prime] (k : Type u)
    [Field k] [CharP k p] [PerfectRing k p]
    (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom] (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n →ₛₗ[
      (PeriodInvariants.CrystallineFrobenius.scalarFrobenius p k).toRingHom]
      AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n :=
  (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv n).toLinearMap.comp
    ((PeriodInvariants.CrystallineFrobenius.rationalFrobenius p k X n).comp
      (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv n).symm.toLinearMap)

variable (q : ℕ) [Fact q.Prime]
  (X : Over (Spec (CommRingCat.of (ZMod q)))) [IsSeparated X.hom]

theorem canonicalSmallFrobenius_eq_pullback (n : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X n) :
    canonicalSmallFrobenius q (ZMod q) X n x =
      CanonicalSmallPullback.CrystallineAdapter.canonicalSmallPullback q (ZMod q) (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X) n x :=
  congrArg (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := X) n)
    (PeriodInvariantsFrobeniusPullback.Crystalline.e61RationalFrobenius_eq_pullback q X n
      ((SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv (p := q) (k := ZMod q) (X := X) n).symm x))

theorem canonicalSmallFrobenius_eq_native
    (x : AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1) :
    canonicalSmallFrobenius q (ZMod q) X 1 x = SmallCrystallineOperators.CrystallineAdapter.smallFrobenius q X x :=
  (canonicalSmallFrobenius_eq_pullback q X 1 x).trans
    (LinearMap.congr_fun (CanonicalSmallPullback.CrystallineAdapter.smallPullback_eq_canonical q
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) X)).symm x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallFrobenius.CrystallineAdapter
