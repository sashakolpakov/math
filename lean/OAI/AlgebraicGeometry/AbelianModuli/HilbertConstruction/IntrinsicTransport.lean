import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableProjectiveTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineFamily
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.IntersectionMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineTransportNaturality

/-! # Intrinsic Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport

noncomputable section

/-! Native universal-family transports on arbitrary Noetherian
affine tests of an actual Hilbert chart intersection. The base
morphism is retained without a chosen coefficient algebra. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {C : Type u} [CommRing C] [IsNoetherianRing C]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)

def stableHilbertChartAmbientMap :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)

variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

theorem stableHilbertIntersectionLeftMap_toAmbient :
    StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD ≫ stableHilbertChartAmbientMap R i j D P =
      stableHilbertChartAmbientMap R i (j.intersection k) D P ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k := by
  simpa only [stableHilbertChartAmbientMap, Category.assoc, Stable.RankIntersectionMaps.stableRankIntersectionLeftMap_factor] using
    congrArg (fun b => b ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P))
      (StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap_factor R i j k D P hP hD)

theorem stableHilbertIntersectionRightMap_toAmbient :
    StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD ≫ stableHilbertChartAmbientMap R i k D P =
      stableHilbertChartAmbientMap R i (j.intersection k) D P ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k := by
  simpa only [stableHilbertChartAmbientMap, Category.assoc, Stable.RankIntersectionMaps.stableRankIntersectionRightMap_factor] using
    congrArg (fun b => b ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i k D (Stable.ConfigurationLocus.configurationHilbertRank D P))
      (StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap_factor R i j k D P hP hD)

variable {f : Spec (.of C) ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)

theorem rawHilbertNativeTransport_existsUnique :
    let F := StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i j D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    let G := StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i k D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
    let E := StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (a ≫ stableHilbertChartAmbientMap R i (j.intersection k) D P)
    ∃! e : Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f F ≅ Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f G,
      e.hom.left ≫ G.val.subschemeι = F.val.subschemeι ≫ Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f E := by
  let I := StableHilbert.AffineFamily.stableHilbertAffineIdeal R (.of C) i j D P hP
    (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
  let J := StableHilbert.AffineFamily.stableHilbertAffineIdeal R (.of C) i k D P hP
    (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
  have hI := StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R (.of C) i j D P hP
    (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) hD
  have hJ := StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R (.of C) i k D P hP
    (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) hD
  change (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)
    ((a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫ stableHilbertChartAmbientMap R i j D P)) D).ker =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D at hI
  change (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C)
    ((a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫ stableHilbertChartAmbientMap R i k D P)) D).ker =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations J.ideal.toIdeal D at hJ
  rw [Category.assoc, stableHilbertIntersectionLeftMap_toAmbient, ← Category.assoc] at hI
  rw [Category.assoc, stableHilbertIntersectionRightMap_toAmbient, ← Category.assoc] at hJ
  have H := Configuration.FamilyTransport.configurationHilbertFamilyTransport_existsUnique I J _ _ D hD hI hJ
    (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k
      (a ≫ stableHilbertChartAmbientMap R i (j.intersection k) D P))
  exact Intrinsic.AffineFamilyTransport.affineNativeFamilyTransport_existsUnique n f _ _ _ H.exists

def rawHilbertNativeTransport :
    Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i j D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)) ≅
    Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i k D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)) :=
  (rawHilbertNativeTransport_existsUnique R i j k D P hP hD a).choose

theorem rawHilbertNativeTransport_ambient :
    (rawHilbertNativeTransport R i j k D P hP hD a).hom.left ≫
        (StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i k D P
          (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)).val.subschemeι =
      (StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i j D P
        (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)).val.subschemeι ≫
      Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
        (a ≫ stableHilbertChartAmbientMap R i (j.intersection k) D P)) :=
  (rawHilbertNativeTransport_existsUnique R i j k D P hP hD a).choose_spec.1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport
