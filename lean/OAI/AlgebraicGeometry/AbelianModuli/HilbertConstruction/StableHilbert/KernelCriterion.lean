import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.ClassifierKernelReflection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedIdealCoordinateLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineParameterCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalClassification

/-! # Kernel Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.KernelCriterion

noncomputable section

/-! Over Noetherian affine tests, the stable Hilbert locus is
exactly the condition that the polynomial matrix kernel is the
fixed-degree relation module of an actual saturated flat Hilbert ideal. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (C : CommRingCat.{u}) [IsNoetherianRing C] {n m : ℕ} (i : Fin m)
variable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable {f : Spec C ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
variable (y : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P))
variable (hy : y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P) = x)

include hP hD hy

theorem stableConfigurationHilbertLift_iff_kernelIdeal :
    (∃! a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P = y) ↔
    ∃ I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n P,
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D)).ker =
        HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D := by
  have : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P) := Over.mono_of_mono_left _
  constructor
  · rintro ⟨a, ha, _⟩
    let z := a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P
    let F := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) z
      (HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P))
    let I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n P := {
      ideal := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
      saturated := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F
      flat := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
      hilbert := HilbertScheme.Presentations.Noetherian.LocalClassification.GradedHilbert.boundedHilbertUniversalFamily_residue_polynomial _ P hP f z }
    have hQ : HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f F P I.hilbert D hD
        (ULift.{u} (Fin (Stable.ConfigurationLocus.configurationHilbertRank D P))) (by simp) =
        TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD := Module.Grassmannian.ext rfl
    have hz : z ≫ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) =
        HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD) := by
      have H := HilbertScheme.Presentations.Noetherian.AffineParameterCoordinates.GradedHilbert.noetherianAffine_hilbert_parameter_coordinates f F P I.hilbert hD
        (ι := ULift.{u} (Fin (Stable.ConfigurationLocus.configurationHilbertRank D P))) (by simp) z rfl
      have hdec :
          (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
            @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
              (fun a b => Subtype.instDecidableEq a b) a b) =
            (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
              @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
                (Homogeneous.Coordinates.homogeneousMonomials_decidableEq (Fin (n + 1)) D) a b) := Subsingleton.elim _ _
      simp only [HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint, hQ] at H
      rw [hdec] at H
      exact H
    have hc : y ≫ HilbertConstruction.Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P) =
        HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD) := by
      rw [← ha, Category.assoc, Stable.ConfigurationLocus.stableConfigurationHilbert_parameter_condition, ← Category.assoc]
      exact hz
    refine ⟨I, ?_⟩
    exact ((HilbertConstruction.Matrix.ClassifierKernelReflection.stablePolynomialKernelClassifier_affine_iff_kernel R i j D _ C x y hy
      (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD)).mp hc).symm
  · rintro ⟨I, hI⟩
    obtain ⟨z, hz, _⟩ := I.existsUnique_hilbert_coordinate_lift f D hD
    have hc : y ≫ HilbertConstruction.Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P) =
        z ≫ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) :=
      (Stable.KernelClassifierFormula.stablePolynomialKernelClassifier_affine_of_kernel R i j D _ C x y hy
        (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD) hI.symm).trans hz.symm
    let a := (Stable.ConfigurationLocus.stableConfigurationHilbertPointEquiv R i j D P (Over.mk f)).symm ⟨(y, z), hc⟩
    have ha : a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P = y :=
      congrArg (fun p => p.val.1)
        ((Stable.ConfigurationLocus.stableConfigurationHilbertPointEquiv R i j D P (Over.mk f)).apply_symm_apply ⟨(y, z), hc⟩)
    exact ⟨a, ha, fun b hb => (cancel_mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P)).mp
      (hb.trans ha.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.KernelCriterion
