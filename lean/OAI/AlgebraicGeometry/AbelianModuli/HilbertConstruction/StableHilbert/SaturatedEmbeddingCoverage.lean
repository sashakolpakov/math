import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.HomogeneousCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PowerEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ScalarCoordinateCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbedding

/-! # Saturated Embedding Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedEmbeddingCoverage.StableHilbertCoverage

noncomputable section

/-! The original normalized uniform embedding has an actual saturated
flat Hilbert ideal with the uniform polynomial. Its source isomorphism,
twisting isomorphism, and all ordered torsion coordinates are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbedding.PolarizedAbelianWithLevel

private theorem precompose_ambient_comparison
    {C₀ : Type*} [Category* C₀] {W X Y Z V : C₀}
    (s : W ⟶ X) (e : X ⟶ Y) (j : Y ⟶ Z) (q : Z ⟶ V) (p : X ⟶ V)
    (h : (e ≫ j) ≫ q = p) : ((s ≫ e) ≫ j) ≫ q = s ≫ p := by
  simpa only [Category.assoc] using congrArg (fun a => s ≫ a) h

namespace UniformEmbeddingModel
variable {C : CommRingCat.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec C, ⊤)))
variable (hd : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)

local instance embedding_closed : IsClosedImmersion E.projectivePresentation.embedding.left :=
  E.projectivePresentation.closedImmersion

def ideal : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C E.dimension (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) := by
  let F := A.graphPowerEmbeddingHilbertFamily hg hN hunit E
  let I := (F.affineFamily (𝟙 (Spec C))).saturatedIdeal
  exact {
    ideal := I.ideal
    saturated := I.saturated
    flat := I.flat
    hilbert := fun p => by
      simpa only [Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial, hd] using I.hilbert p }

theorem ideal_eq : (UniformEmbeddingModel.ideal A E hg hN hunit hd).ideal =
    HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.ideal E.projectivePresentation.embedding := rfl

def iso : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (UniformEmbeddingModel.ideal A E hg hN hunit hd).ideal :=
  HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.iso E.projectivePresentation.embedding

theorem embedding :
    (((iso A E hg hN hunit hd).hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (UniformEmbeddingModel.ideal A E hg hN hunit hd).ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec C)) E.dimension) = E.projectivePresentation.embedding.left :=
  HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.embedding E.projectivePresentation.embedding

def twistingIso :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle (UniformEmbeddingModel.ideal A E hg hN hunit hd).ideal 1).pullback
      (iso A E hg hN hunit hd).hom.left).sheaf ≅
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf :=
  HomogeneousCoverage.StableHilbertCoverage.EmbeddingModel.twistingIso E.projectivePresentation.embedding ≪≫ E.sectionData.twistingIso ≪≫
    E.canonicalDegreeIso (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) hd

end UniformEmbeddingModel

namespace NormalizedGraphEmbedding
variable (R : Type u) [CommRing R] {C : CommRingCat.{u}}
    {f : Spec C ⟶ Spec (.of R)} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C)} {i : Fin (N ^ (2 * g))}
    (D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk f) A i)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(Spec C, ⊤)))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.saturatedIdeal : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C D.embedding.dimension
    (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) :=
  UniformEmbeddingModel.ideal A D.embedding hg hN hunit D.degree_eq

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.homogeneousIso : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (D.saturatedIdeal R hg hN hunit).ideal :=
  UniformEmbeddingModel.iso A D.embedding hg hN hunit D.degree_eq

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.homogeneousTwistingIso :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle (D.saturatedIdeal R hg hN hunit).ideal 1).pullback
      (D.homogeneousIso R hg hN hunit).hom.left).sheaf ≅
        (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf :=
  UniformEmbeddingModel.twistingIso A D.embedding hg hN hunit D.degree_eq

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.homogeneous_embedding :
    (((D.homogeneousIso R hg hN hunit).hom.left ≫
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (D.saturatedIdeal R hg hN hunit).ideal) ≫
        AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec C)) D.embedding.dimension) =
      D.embedding.projectivePresentation.embedding.left :=
  UniformEmbeddingModel.embedding A D.embedding hg hN hunit D.degree_eq

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.homogeneous_markedPoint (z : Fin (N ^ (2 * g))) :
    (A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫
      (D.homogeneousIso R hg hN hunit).hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (D.saturatedIdeal R hg hN hunit).ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i D.chartIndex C D.chartPoint ⟨z⟩)
        (D.chartIndex.coordinate z)
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i D.chartIndex C D.chartPoint ⟨z⟩) := by
  let j := D.chartIndex
  let ρ := D.chartPoint.left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom
  let v := fun k => ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete z k)
  have hv : ∀ x : Spec C, ∃ k, x ∈ (Spec C).basicOpen (v k) :=
    Balanced.FrameChartProjectivePoints.balancedFrameChartProjectiveCoordinates_cover R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete (Spec C) ρ z
  have hi : v (j.coordinate z) = 1 := by
    change ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete z (j.coordinate z)) = 1
    rw [Balanced.FrameChartNormalization.balancedFrameChartVectors_selected, map_one]
  let q : (Projective.ProjectivePresentations.affineProjectiveSpace C D.embedding.dimension).left ⟶
      (Projective.ProjectivePresentations.projectiveSpaceOver (Spec C) D.embedding.dimension).left :=
    AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec C)) D.embedding.dimension
  let : IsIso q := (AffineProjective.Charts.affineProjectiveChartMap_isPullback (𝟙 (Spec C)) D.embedding.dimension).isIso_fst_of_isIso
  have hmark : A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫
      D.embedding.projectivePresentation.embedding.left =
        (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left :=
    congrArg Over.Hom.left (D.marked z)
  have hcoordinate : (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i D.chartIndex C D.chartPoint ⟨z⟩)
        (D.chartIndex.coordinate z)
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i D.chartIndex C D.chartPoint ⟨z⟩) ≫ q :=
    ScalarCoordinateCoverage.StableHilbertCoverage.scalarCoordinateProjectivePoint_affine C v hv (j.coordinate z) hi
  apply (cancel_mono q).mp
  have hembedding : ((A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫
      (D.homogeneousIso R hg hN hunit).hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (D.saturatedIdeal R hg hN hunit).ideal) ≫ q =
      A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫
        D.embedding.projectivePresentation.embedding.left :=
    precompose_ambient_comparison
      (A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z))
      (D.homogeneousIso R hg hN hunit).hom.left
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (D.saturatedIdeal R hg hN hunit).ideal) q
      D.embedding.projectivePresentation.embedding.left (D.homogeneous_embedding R hg hN hunit)
  exact hembedding.trans (hmark.trans hcoordinate)

end NormalizedGraphEmbedding

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedEmbeddingCoverage.StableHilbertCoverage
