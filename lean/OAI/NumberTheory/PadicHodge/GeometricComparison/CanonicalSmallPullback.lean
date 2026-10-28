import OAI.NumberTheory.PadicHodge.GeometricComparison.PeriodInvariantsPullbackAdapter

/-! # Canonical Small Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallPullback.CrystallineAdapter

noncomputable section

/-! A named normalization of the ordinary native small-site crystalline pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def canonicalSmallPullback (p : ℕ) [Fact p.Prime] (k : Type u)
    [Field k] [CharP k p] [PerfectRing k p]
    {X Y : Over (Spec (CommRingCat.of k))} [IsSeparated X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (n : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k Y n →ₗ[FractionRing (WittVector p k)]
      AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n :=
  (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv n).toLinearMap.comp
    ((PeriodInvariants.CrystallinePullback.rationalPullback p k f n).comp
      (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.rationalEquiv n).symm.toLinearMap)

theorem smallPullback_eq_canonical (q : ℕ) [Fact q.Prime]
    {X Y : Over (Spec (CommRingCat.of (ZMod q)))} [IsSeparated X.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) : SmallCrystallineOperators.CrystallineAdapter.smallPullback q f = canonicalSmallPullback q (ZMod q) f 1 :=
  PeriodInvariantsPullbackAdapter.CrystallineAdapter.smallPullback_eq_native_conjugate q f

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallPullback.CrystallineAdapter
