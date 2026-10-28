import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartPullbacks

/-! # Compatible Chart Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleChartFrames

noncomputable section

/-! Any two affine Hilbert chart points with the same global
rank parameter have frame-related configurations. This compares
arbitrary pairs and triples without selecting a common chart in advance. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ) (C : CommRingCat.{u})
variable {f : Spec C ⟶ Spec (.of R)}

def affineHilbertChartVectors (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    ULift.{u} (Fin m) → Fin (n + 1) → C :=
  Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D P)

omit [IsNoetherianRing R] in
theorem affineHilbertChartVectors_hasFrame
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun C (Fin (n + 1)))
      (fun t => affineHilbertChartVectors R i j D P C a ⟨j.frame t⟩)
      (affineHilbertChartVectors R i j D P C a ⟨j.additional⟩)) :=
  StableChartFrames.stablePolynomialChartPointVectors_hasFrame R i j (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D P)

private theorem affineHilbertChartAmbient_left
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (ha : c ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD = a) :
    a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D P =
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k := by
  rw [← ha, Category.assoc, IntrinsicTransport.stableHilbertIntersectionLeftMap_toAmbient, ← Category.assoc]

private theorem affineHilbertChartAmbient_right
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (ha : c ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD = a) :
    a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i k D P =
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k := by
  rw [← ha, Category.assoc, IntrinsicTransport.stableHilbertIntersectionRightMap_toAmbient, ← Category.assoc]

private theorem affineHilbertChartVectors_common
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (ha : c ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD = a)
    (hb : c ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD = b) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated (affineHilbertChartVectors R i j D P C a)
      (affineHilbertChartVectors R i k D P C b) := by
  have hj := affineHilbertChartAmbient_left R i j k D P C hP hD a c ha
  have hk := affineHilbertChartAmbient_right R i j k D P C hP hD b c hb
  unfold affineHilbertChartVectors
  rw [hj, hk]
  exact StableChartFrames.stablePolynomialIntersection_frameRelated R i j k
    (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)

theorem affineHilbertChartVectors_related
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
    (h : a ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i k D P) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated (affineHilbertChartVectors R i j D P C a)
      (affineHilbertChartVectors R i k D P C b) := by
  let H := StableHilbert.ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD
  exact affineHilbertChartVectors_common R i j k D P C hP hD a b (H.lift a b h)
    (H.lift_fst _ _ _) (H.lift_snd _ _ _)

omit [IsNoetherianRing R] in
theorem affineHilbertChartVectors_coefficient
    {A : Type u} [CommRing A] (φ : C →+* A)
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    affineHilbertChartVectors R i j D P (.of A) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ a) =
      fun c t => φ (affineHilbertChartVectors R i j D P C a c t) := by
  simpa only [affineHilbertChartVectors, Category.assoc] using
    StableChartFrames.stablePolynomialChartPointVectors_coefficient R i j (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D P) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleChartFrames
