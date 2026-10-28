import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.KernelClassifierFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionStableRankLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CoordinateRelations

/-! # Torsion Stable Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionStableCoordinates

noncomputable section

/-! The stable-chart classifier of an actual high auxiliary torsion
configuration is the canonical uniform Hilbert coordinate point of
the embedded family. The identity holds over every noetherian ring
whenever the configuration has a lift to the genuine rank locus. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def configurationHilbertCoordinatePoint
    {C : Type u} [CommRing C] [IsNoetherianRing C] {r : ℕ} {P : Polynomial ℚ}
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C r P) (D : ℕ)
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D) :
    Module.Grassmannian C (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} r D → C)
      (Fintype.card (ULift.{u} (Fin (P.eval (D : ℚ)).num.toNat))) := by
  haveI : Module.Projective C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) :=
    HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I.ideal I.saturated P I.hilbert D
      ((le_max_left _ _).trans hdegree)
  exact HilbertScheme.Presentations.DegreeCoordinateGrassmannian.GradedHilbert.degreeCoordinateGrassmannian I.ideal (fun p =>
    (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I.ideal I.saturated P I.hilbert D hdegree p).trans (by simp))

variable (R : Type u) [CommRing R] (C : CommRingCat.{u}) [IsNoetherianRing C]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (i : Fin (n ^ (2 * g)))
variable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (r + 1) (n ^ (2 * g)))
variable {f : Spec C ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C r P)
variable (e : A.abelian.scheme ≅ HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec C, ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (hpoints : ∀ c : ULift.{u} (Fin (n ^ (2 * g))),
  (A.abelian.fullLevelGlobalSection level (Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration c) ≫ e.hom.left) ≫
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x c)
        (j.coordinate c.down) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x c))

include A I e eL hg hδ hN hunit level hD hlarge hpoints

theorem auxiliaryTorsionStableChart_coordinate_kernel :
    (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D)).ker =
      HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D := by
  let ℓ := Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration (g := g) (n := n)
  let w := fun c => Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x (ℓ.symm c)
  let selected := fun c => j.coordinate (ℓ.symm c).down
  have hselected : ∀ c, w c (selected c) = 1 :=
    fun c => Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x (ℓ.symm c)
  have hw : ∀ c,
      (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
        AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (w c) (selected c) (hselected c) := by
    intro c
    have hc :
        (A.abelian.fullLevelGlobalSection level (ℓ (ℓ.symm c)) ≫ e.hom.left) ≫
          HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
        AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (w c) (selected c) (hselected c) :=
      hpoints (ℓ.symm c)
    rw [ℓ.apply_symm_apply] at hc
    exact hc
  have he : (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) D)).ker =
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).ker := by
    have hrel := Configuration.CoordinateRelations.configurationMonomialMatrix_kernel_relabel w D ℓ
    have hwvec : (fun c => w (ℓ c)) = Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x := by
      funext c
      exact congrArg (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) (ℓ.symm_apply_apply c)
    rw [hwvec] at hrel
    exact hrel
  exact he.trans (Configuration.CoordinateRelations.auxiliaryTorsionConfiguration_coordinate_kernel A I e eL
    hg hδ hN hunit level D hD hlarge w selected hselected hw)

theorem auxiliaryTorsionStableChart_classifier_eq
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
    (y : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (P.eval (D : ℚ)).num.toNat)
    (hy : y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (P.eval (D : ℚ)).num.toNat = x) :
    y ≫ HilbertConstruction.Matrix.RankKernelClassifier.stableConfigurationPolynomialKernelClassifier R i j D (P.eval (D : ℚ)).num.toNat =
      HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (configurationHilbertCoordinatePoint I D hdegree) := by
  apply Stable.KernelClassifierFormula.stablePolynomialKernelClassifier_affine_of_kernel R i j D _ C x y hy
  exact (auxiliaryTorsionStableChart_coordinate_kernel R C i j x A I e eL
    hg hδ hN hunit level D hD hlarge hpoints).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionStableCoordinates
