import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.Intersection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.MonoLocusTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts

/-! # Intersection Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps

noncomputable section

/-! The actual Hilbert loci on stable rank-chart intersections
map to both chart Hilbert loci. These are open immersions and
their squares with the rank restriction maps are Cartesian on all tests. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

def stableHilbertIntersectionLeftMap :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P :=
  Noetherian.MonoLocusTransport.noetherianMonoLocusTransport
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P)
    (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (fun T hT y => by
      let := hT
      exact Noetherian.Intersection.noetherianHilbertIntersection_left_iff R i j k D P hP hD T y)

theorem stableHilbertIntersectionLeftMap_factor :
    stableHilbertIntersectionLeftMap R i j k D P hP hD ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P =
      Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P ≫
        Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P) :=
  Noetherian.MonoLocusTransport.noetherianMonoLocusTransport_factor _ _ _ _

theorem stableHilbertIntersectionLeft_isPullback :
    IsPullback (stableHilbertIntersectionLeftMap R i j k D P hP hD)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)
      (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) := by
  have : IsLocallyNoetherian (pullback (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)
      (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))).left :=
    NoetherianCharts.overPullback_locallyNoetherian_of_open _ _
  exact Noetherian.MonoLocusTransport.noetherianMonoLocusTransport_isPullback _ _ _ _

instance stableHilbertIntersectionLeftMap_open :
    IsOpenImmersion (stableHilbertIntersectionLeftMap R i j k D P hP hD).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((stableHilbertIntersectionLeft_isPullback R i j k D P hP hD).map (Over.forget (Spec (.of R)))).flip
    (inferInstanceAs (IsOpenImmersion
      (Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)).left))

def stableHilbertIntersectionRightMap :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P :=
  Noetherian.MonoLocusTransport.noetherianMonoLocusTransport
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P)
    (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (fun T hT y => by
      let := hT
      exact Noetherian.Intersection.noetherianHilbertIntersection_right_iff R i j k D P hP hD T y)

theorem stableHilbertIntersectionRightMap_factor :
    stableHilbertIntersectionRightMap R i j k D P hP hD ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P =
      Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P ≫
        Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P) :=
  Noetherian.MonoLocusTransport.noetherianMonoLocusTransport_factor _ _ _ _

theorem stableHilbertIntersectionRight_isPullback :
    IsPullback (stableHilbertIntersectionRightMap R i j k D P hP hD)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P)
      (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P)
      (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) := by
  have : IsLocallyNoetherian (pullback (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P)
      (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P))).left :=
    NoetherianCharts.overPullback_locallyNoetherian_of_open _ _
  exact Noetherian.MonoLocusTransport.noetherianMonoLocusTransport_isPullback _ _ _ _

instance stableHilbertIntersectionRightMap_open :
    IsOpenImmersion (stableHilbertIntersectionRightMap R i j k D P hP hD).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((stableHilbertIntersectionRight_isPullback R i j k D P hP hD).map (Over.forget (Spec (.of R)))).flip
    (inferInstanceAs (IsOpenImmersion
      (Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)).left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps
