import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IntersectionBaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableIntersection.ProjectiveTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality

/-! # Stable Chart Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableChartFrames

noncomputable section

/-! Raw affine chart vectors have projective frames and actual
intersection orbit relations for every base morphism Spec C → Spec R.
Their coefficient naturality uses the spectrum/global-sections identity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {C A : Type u} [CommRing C] [CommRing A]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {f : Spec (.of C) ⟶ Spec (.of R)}

theorem stablePolynomialChartPointCoefficients_coefficient
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (φ : C →+* A) :
    Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointCoefficients R i j (.of A) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ x) =
      φ.comp (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointCoefficients R i j (.of C) x) := by
  ext z
  change (Scheme.ΓSpecIso (.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ) ≫ x.left).appTop
        ((Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv z)) = _
  rw [Scheme.Hom.comp_appTop]
  exact congrArg (fun b : Γ(Spec (.of C), ⊤) ⟶ CommRingCat.of A =>
    b (x.left.appTop ((Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv z)))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem stablePolynomialChartPointVectors_coefficient
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) (φ : C →+* A) :
    Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of A) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ x) =
      fun c t => φ (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x c t) := by
  unfold Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors
  rw [stablePolynomialChartPointCoefficients_coefficient]
  rfl

theorem stablePolynomialChartPointVectors_coefficientAlgebra
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    letI := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
    Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x =
      fun c : ULift.{u} (Fin m) => Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        (Stable.AffineRelations.stableChartAffineAlgebraPoint R i j ((Affine.IntersectionBaseMaps.affineOverCoefficientIso R C f).inv ≫ x)) c.down := by
  let := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
  have he : ((Affine.IntersectionBaseMaps.affineOverCoefficientIso R C f).inv ≫ x).left = x.left := by
    change (𝟙 _) ≫ x.left = x.left
    exact Category.id_comp _
  rw [← Stable.AffineRelations.stableChartAffineAlgebraPoint_vectors]
  unfold Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointCoefficients
  rw [he]

theorem stablePolynomialChartPointVectors_hasFrame
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun C (Fin (n + 1)))
      (fun t => Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x ⟨j.frame t⟩)
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x ⟨j.additional⟩)) := by
  let := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
  rw [stablePolynomialChartPointVectors_coefficientAlgebra]
  exact Stable.NormalizedFrameRelation.stableChartNormalizedPoint_hasFrame R i j _

private theorem intersection_left_vectors
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :
    letI := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
    Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k) =
      fun c : ULift.{u} (Fin m) => Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i j
        ((Stable.AffineRelations.stableChartAffineAlgebraPoint R i (j.intersection k) ((Affine.IntersectionBaseMaps.affineOverCoefficientIso R C f).inv ≫ x)).comp
          (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionLeftAlg R i j.exponent k.exponent j.balanced k.balanced)) c.down := by
  let := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
  rw [stablePolynomialChartPointVectors_coefficientAlgebra]
  simp only [← Category.assoc, Stable.AffineRelations.stableChartAffineAlgebraPoint, StableIntersection.SchemeRank.stableChartIntersectionLeftOver]
  rw [Stable.AffineRelations.stableChartAffineAlgebraPoint_intersection_left]
  rfl

private theorem intersection_right_vectors
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :
    letI := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
    Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k) =
      fun c : ULift.{u} (Fin m) => Stable.ChartNormalizedRankPoints.stableChartNormalizedPointVectors R i k
        ((Stable.AffineRelations.stableChartAffineAlgebraPoint R i (j.intersection k) ((Affine.IntersectionBaseMaps.affineOverCoefficientIso R C f).inv ≫ x)).comp
          (Balanced.IntersectionAlgebraMaps.balancedChartIntersectionRightAlg R i j.exponent k.exponent j.balanced k.balanced)) c.down := by
  let := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
  rw [stablePolynomialChartPointVectors_coefficientAlgebra]
  simp only [← Category.assoc, Stable.AffineRelations.stableChartAffineAlgebraPoint, StableIntersection.SchemeRank.stableChartIntersectionRightOver]
  rw [Stable.AffineRelations.stableChartAffineAlgebraPoint_intersection_right]
  rfl

theorem stablePolynomialIntersection_frameRelated
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i (j.intersection k)) :
    Configuration.ProjectiveTransport.ConfigurationFrameRelated
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k))
      (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k)) := by
  let := Affine.IntersectionBaseMaps.affineOverCoefficientAlgebra R C f
  let x' := (Affine.IntersectionBaseMaps.affineOverCoefficientIso R C f).inv ≫ x
  let ρ := Stable.AffineRelations.stableChartAffineAlgebraPoint R i (j.intersection k) x'
  have hj := intersection_left_vectors R i j k x
  have hk := intersection_right_vectors R i j k x
  rw [hj, hk]
  obtain ⟨T, s, hs⟩ := StableIntersection.ProjectiveTransport.stableChartIntersection_frameRelated R i j k ρ
  exact ⟨T, fun c => s c.down, fun c => hs c.down⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableChartFrames
