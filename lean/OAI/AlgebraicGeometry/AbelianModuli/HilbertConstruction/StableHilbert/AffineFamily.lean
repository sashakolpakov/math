import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.KernelCriterion

/-! # Affine Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineFamily

noncomputable section

/-! The actual universal family at a Noetherian affine point of
a stable Hilbert chart has a canonical saturated flat ideal. Its
degree relations are exactly the configuration evaluation kernel. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (C : CommRingCat.{u}) [IsNoetherianRing C] {n m : ℕ} (i : Fin m)
variable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (P : Polynomial ℚ)
variable {f : Spec C ⟶ Spec (.of R)}

def stableHilbertAffineFamily (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (Over.mk f) :=
  HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P)
    (HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily n D (Spec (.of R)) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P))

omit [IsNoetherianRing C] in
theorem stableHilbertAffineFamily_pullback
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    stableHilbertAffineFamily R C i j D P a =
      HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) := by
  exact HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp _ _ _ _

variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)

def stableHilbertAffineIdeal (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n P where
  ideal := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (stableHilbertAffineFamily R C i j D P a)
  saturated := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f _
  flat := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f _
  hilbert := HilbertScheme.Presentations.Noetherian.LocalClassification.GradedHilbert.boundedHilbertUniversalFamily_residue_polynomial _ P hP f
    (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P)

theorem stableHilbertAffineIdeal_native
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    (stableHilbertAffineIdeal R C i j D P hP a).nativeHilbertFamily f =
      stableHilbertAffineFamily R C i j D P a := by
  apply HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n f
  exact (stableHilbertAffineIdeal R C i j D P hP a).nativeHilbertFamily_coordinates f

theorem stableHilbertAffineIdeal_matrix_kernel
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D) :
    (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C
        (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
          Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P))) D)).ker =
      HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (stableHilbertAffineIdeal R C i j D P hP a).ideal D := by
  let I := stableHilbertAffineIdeal R C i j D P hP a
  let F := stableHilbertAffineFamily R C i j D P a
  let z := a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P
  let y := a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P
  let x := y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)
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
    change (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P) ≫ _ = _
    rw [Category.assoc, Stable.ConfigurationLocus.stableConfigurationHilbert_parameter_condition, ← Category.assoc]
    exact hz
  have H := ((HilbertConstruction.Matrix.ClassifierKernelReflection.stablePolynomialKernelClassifier_affine_iff_kernel R i j D _ C x y rfl
    (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hD)).mp hc).symm
  change _ = HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D at H
  simpa only [x, y, Category.assoc] using H

theorem stableHilbertAffineIdeal_evaluation_kernel
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D) :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C
        (a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
          Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P))) D).ker =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (stableHilbertAffineIdeal R C i j D P hP a).ideal.toIdeal D := by
  apply Submodule.map_injective_of_injective (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis C n D).equivFun.injective
  exact (Configuration.CoordinateRelations.configurationMonomialMatrix_kernel _ D).symm.trans
    (stableHilbertAffineIdeal_matrix_kernel R C i j D P hP a hD)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineFamily
