import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleChartFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyCocycle

/-! # Chart Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartTransport

noncomputable section

/-! Compatible affine Hilbert chart points carry canonical native
family transports. These satisfy the full cocycle and identity
laws, with actual projective-frame changes determining their embeddings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (C : CommRingCat.{u}) [IsNoetherianRing C] {f : Spec C ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
variable (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
variable (h : a ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i j D P = b ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i k D P)

def affineHilbertChartFamilyTransport :
    Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i j D P a) ≅
      Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i k D P b) :=
  Intrinsic.AffineFamilyTransport.affineNativeFamilyTransport n f _ _
    (Configuration.FamilyTransport.configurationHilbertFamilyTransport
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i j D P hP a) (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i k D P hP b)
      (CompatibleChartFrames.affineHilbertChartVectors R i j D P C a) (CompatibleChartFrames.affineHilbertChartVectors R i k D P C b) D hD
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i j D P hP a hD)
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i k D P hP b hD)
      (CompatibleChartFrames.affineHilbertChartVectors_related R i j k D P C hP hD a b h))

theorem affineHilbertChartFamilyTransport_ambient :
    (affineHilbertChartFamilyTransport R i j k D P hP hD C a b h).hom.left ≫
      (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i k D P b).val.subschemeι =
    (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i j D P a).val.subschemeι ≫
      Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f
        (Configuration.ProjectiveTransport.configurationProjectiveTransport (CompatibleChartFrames.affineHilbertChartVectors R i j D P C a)
          (CompatibleChartFrames.affineHilbertChartVectors R i k D P C b)
          (CompatibleChartFrames.affineHilbertChartVectors_related R i j k D P C hP hD a b h)) := by
  apply Intrinsic.AffineFamilyTransport.affineNativeFamilyTransport_ambient
  exact Configuration.FamilyTransport.configurationHilbertFamilyTransport_ambient
    (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i j D P hP a) (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i k D P hP b)
    (CompatibleChartFrames.affineHilbertChartVectors R i j D P C a) (CompatibleChartFrames.affineHilbertChartVectors R i k D P C b) D hD
    (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i j D P hP a hD)
    (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i k D P hP b hD)
    (CompatibleChartFrames.affineHilbertChartVectors_related R i j k D P C hP hD a b h)

theorem affineHilbertChartFamilyTransport_cocycle
    (l : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i l D P)
    (hbc : b ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i k D P = c ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i l D P)
    (hac : a ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i j D P = c ≫ StableHilbert.ChartPullbacks.stableHilbertChartToRank R i l D P) :
    affineHilbertChartFamilyTransport R i j k D P hP hD C a b h ≪≫
      affineHilbertChartFamilyTransport R i k l D P hP hD C b c hbc =
    affineHilbertChartFamilyTransport R i j l D P hP hD C a c hac := by
  unfold affineHilbertChartFamilyTransport
  rw [Intrinsic.AffineFamilyComposition.affineNativeFamilyTransport_trans]
  exact congrArg (Intrinsic.AffineFamilyTransport.affineNativeFamilyTransport n f
    (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i j D P a) (StableHilbert.AffineFamily.stableHilbertAffineFamily R C i l D P c))
    (Configuration.FamilyCocycle.configurationHilbertFamilyTransport_cocycle
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i j D P hP a) (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i k D P hP b)
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i l D P hP c)
      (CompatibleChartFrames.affineHilbertChartVectors R i j D P C a) (CompatibleChartFrames.affineHilbertChartVectors R i k D P C b)
      (CompatibleChartFrames.affineHilbertChartVectors R i l D P C c) D hD
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i j D P hP a hD)
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i k D P hP b hD)
      (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i l D P hP c hD)
      (CompatibleChartFrames.affineHilbertChartVectors_related R i j k D P C hP hD a b h)
      (CompatibleChartFrames.affineHilbertChartVectors_related R i k l D P C hP hD b c hbc)
      (CompatibleChartFrames.affineHilbertChartVectors_related R i j l D P C hP hD a c hac)
      (fun t => ⟨j.frame t⟩) (fun t => ⟨k.frame t⟩) ⟨j.additional⟩ ⟨k.additional⟩
      (CompatibleChartFrames.affineHilbertChartVectors_hasFrame R i j D P C a)
      (CompatibleChartFrames.affineHilbertChartVectors_hasFrame R i k D P C b))

theorem affineHilbertChartFamilyTransport_self :
    affineHilbertChartFamilyTransport R i j j D P hP hD C a a rfl = Iso.refl _ := by
  unfold affineHilbertChartFamilyTransport
  rw [Configuration.FamilyCocycle.configurationHilbertFamilyTransport_self
    (StableHilbert.AffineFamily.stableHilbertAffineIdeal R C i j D P hP a) (CompatibleChartFrames.affineHilbertChartVectors R i j D P C a)
    D hD (StableHilbert.AffineFamily.stableHilbertAffineIdeal_evaluation_kernel R C i j D P hP a hD)
    (CompatibleChartFrames.affineHilbertChartVectors_related R i j j D P C hP hD a a rfl)
    (fun t => ⟨j.frame t⟩) ⟨j.additional⟩ (CompatibleChartFrames.affineHilbertChartVectors_hasFrame R i j D P C a)]
  exact Intrinsic.AffineFamilyComposition.affineNativeFamilyTransport_refl n f _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartTransport
