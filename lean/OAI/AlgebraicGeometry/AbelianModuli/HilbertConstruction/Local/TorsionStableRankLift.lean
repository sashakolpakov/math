import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CokernelRelabeling
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BasisCoordinateFrames

/-! # Torsion Stable Rank Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionStableRankLift

noncomputable section

/-! An actual high auxiliary torsion configuration lying in a stable
balanced chart has a unique lift to its polynomial rank locus over a
noetherian local coefficient ring. The lift uses the full flatness
and rank condition, not only ranks of geometric matrices. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def liftedFullLevelLabelEnumeration {g n : ℕ} [NeZero n] :
    ULift.{u} (Fin (n ^ (2 * g))) ≃ Multiplicative (Fin (2 * g) → ZMod n) :=
  Equiv.ulift.trans (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := n))

variable (R : Type u) [CommRing R]
variable (C : CommRingCat.{u}) [IsNoetherianRing C] [IsLocalRing C]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (i : Fin (n ^ (2 * g)))
variable (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (r + 1) (n ^ (2 * g)))
variable {f : Spec C ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C r P)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec C, ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (hpoints : ∀ c : ULift.{u} (Fin (n ^ (2 * g))),
  (A.abelian.fullLevelGlobalSection level (liftedFullLevelLabelEnumeration c) ≫ e.hom.left) ≫
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x c)
        (j.coordinate c.down) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x c))

include A I e eL hg hδ hN hunit level hD hdegree hlarge hpoints

theorem localAuxiliaryTorsionConfiguration_unique_rankLift :
    ∃! y : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D (P.eval (D : ℚ)).num.toNat,
      y ≫ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (P.eval (D : ℚ)).num.toNat = x := by
  let ℓ := liftedFullLevelLabelEnumeration (g := g) (n := n)
  let w := fun c => Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x (ℓ.symm c)
  let selected := fun c => j.coordinate (ℓ.symm c).down
  have hselected : ∀ c, w c (selected c) = 1 :=
    fun c => Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x (ℓ.symm c)
  have hw : ∀ c,
      (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
        AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (w c) (selected c) (hselected c) := by
    intro c
    have hc : (A.abelian.fullLevelGlobalSection level (ℓ (ℓ.symm c)) ≫ e.hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
        AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (w c) (selected c) (hselected c) := hpoints (ℓ.symm c)
    rw [ℓ.apply_symm_apply] at hc
    exact hc
  have h := TorsionEvaluationRank.localAuxiliaryTorsionMonomialMatrix_flatRank A I e eL hg hδ hN hunit
    level D hD hdegree hlarge w selected hselected hw
  have hrel := (Configuration.CokernelRelabeling.configurationMonomialMatrix_flatRank_relabel_iff
    w D (P.eval (D : ℚ)).num.toNat (n ^ (2 * g)) ℓ).mpr h
  apply (Stable.PolynomialMatrixCoefficients.stablePolynomialRankPoint_iff_configuration R i j C x D (P.eval (D : ℚ)).num.toNat).mpr
  have hwvec : (fun c => w (ℓ c)) = Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x := by
    funext c
    exact congrArg (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x) (ℓ.symm_apply_apply c)
  rw [hwvec] at hrel
  exact hrel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionStableRankLift
