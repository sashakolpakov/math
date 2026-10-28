import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionFamilyIso

/-! # Family Pullbacks -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyPullbacks

noncomputable section

/-! The actual universal chart families and their overlap isomorphisms
are expressed using ordinary scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)

def stableHilbertChartFamily
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Over (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left :=
  Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)

variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

def stableHilbertOverlapFamilyIso
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (Over.pullback (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD).left).obj
        (stableHilbertChartFamily R i D P j) ≅
    (Over.pullback (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD).left).obj
        (stableHilbertChartFamily R i D P k) :=
  (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)).symm ≪≫
  Hilbert.IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD ≪≫
  Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyPullbacks
