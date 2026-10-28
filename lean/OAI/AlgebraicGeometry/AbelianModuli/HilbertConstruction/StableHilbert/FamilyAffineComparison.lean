import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionAffineTransportComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.LiftInduction

/-! # Family Affine Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyAffineComparison

noncomputable section

/-! The actual global stable-family transport becomes the original affine
chart transport under the canonical native-family pullback isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (C : CommRingCat.{u}) [IsNoetherianRing C]
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {f : Spec (.of C) ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
variable (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)

theorem stableHilbertFamilyTransport_affine
    (h : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
      b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P) :
    FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j a ≪≫
        FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b h ≪≫
        (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) k b).symm =
      Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C) a b h :=
  Pullback.LiftInduction.pullbackLift_induction (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (fun a b h =>
      FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j a ≪≫
          FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k a b h ≪≫
          (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) k b).symm =
        Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C) a b h)
    (fun c h => IntersectionAffineTransportComparison.stableHilbertFamilyTransport_intersection_affine R i D P hP hD C j k c h)
    a b h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyAffineComparison
