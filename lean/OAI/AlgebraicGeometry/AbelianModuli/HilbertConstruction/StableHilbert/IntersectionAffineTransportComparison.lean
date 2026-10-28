import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ChartFamilyTransportComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionAffineComparison

/-! # Intersection Affine Transport Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionAffineTransportComparison

noncomputable section

/-! The stable-family transport agrees with the original affine transport
when the two chart points come from a common intersection point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (C : Type u) [CommRing C] [IsNoetherianRing C]
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {f : Spec (.of C) ⟶ Spec (.of R)}
variable (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)

private theorem intersectionAffineRawComparison :
    Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫
      Hilbert.IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD (.of C) c ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm =
      IntrinsicTransport.rawHilbertNativeTransport R (C := C) i j k D P hP hD c :=
  Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso_transport_eq (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD (.of C) c)
    (IntrinsicTransport.rawHilbertNativeTransport R (C := C) i j k D P hP hD c)
    (Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)))
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionAffineTransport_ambient R i j k D P hP hD (.of C) c)
    (IntrinsicTransport.rawHilbertNativeTransport_ambient R (C := C) i j k D P hP hD c)

variable (h : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫
    ChartPullbacks.stableHilbertChartToRank R i j D P =
  (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫
    ChartPullbacks.stableHilbertChartToRank R i k D P)

private theorem intersectionAffineComparison :
    Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫
      Hilbert.IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD (.of C) c ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm =
      Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h :=
  (intersectionAffineRawComparison R i D P hP hD C j k c).trans
    (FamilyTransport.rawHilbertNativeTransport_eq_affine_of R i D P hP hD C j k c h)

omit [IsNoetherianRing C] in
private theorem intersectionNativeComparison :
    FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h ≪≫
      (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) k
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)).symm =
      Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫
      Intrinsic.FamilyPullbackPoints.nativeFamilyIsoPullback (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) c
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD)
        (Hilbert.IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD) ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm :=
  Intrinsic.ChartFamilyTransportComparison.nativeChartFamilyTransportComparison (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D P)
    (Hilbert.IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD)
    (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h c rfl rfl
    (AffineFamily.stableHilbertAffineFamily R (.of C) i j D P
      (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD))
    (AffineFamily.stableHilbertAffineFamily R (.of C) i k D P
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD))
    (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i j D P
      (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD))
    (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i k D P
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD))
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm
    (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm

private theorem intersectionNativeToAffine :
    Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫
      Intrinsic.FamilyPullbackPoints.nativeFamilyIsoPullback (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) c
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD)
        (Hilbert.IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD) ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm =
      Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫
      Hilbert.IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD (.of C) c ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm :=
  congrArg (fun z =>
    Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) c).symm ≪≫ z ≪≫
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Hilbert.IntersectionUniversalFamilies.hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) c).symm).symm)
    (Hilbert.IntersectionAffineComparison.hilbertIntersectionFamilyIso_pullback_affine R i j k D P hP hD (.of C) c)

theorem stableHilbertFamilyTransport_intersection_affine :
    FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) j
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D P hP hD j k
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h ≪≫
      (FamilyTransport.stableHilbertAffinePullbackIso R i D P (.of C) k
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)).symm =
      Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h :=
  (intersectionNativeComparison R i D P hP hD C j k c h).trans
    ((intersectionNativeToAffine R i D P hP hD C j k c).trans
      (intersectionAffineComparison R i D P hP hD C j k c h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionAffineTransportComparison
