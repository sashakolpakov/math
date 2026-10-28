import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionConfigurationDeterminesIdeal

/-! # Torsion Configuration Evaluation Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationEvaluationKernel

noncomputable section

/-! Normalized coordinates of sufficiently high auxiliary torsion
recover the exact homogeneous relation module as a polynomial
evaluation kernel. In the uniform degree range this kernel gives the
actual Hilbert Grassmannian point over a noetherian coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r D : ℕ} {ι : Type v}

structure HomogeneousConfigurationHasRank (w : ι → Fin (r + 1) → R) (D k : ℕ) : Prop where
  finite : Module.Finite R ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker)
  projective : Module.Projective R ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker)
  rank : ∀ p : PrimeSpectrum R,
    Module.rankAtStalk (R := R) ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker) p = k

def homogeneousConfigurationGrassmannian (w : ι → Fin (r + 1) → R) (D k : ℕ)
    (H : HomogeneousConfigurationHasRank w D k) : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) k where
  toSubmodule := (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker
  finite_quotient := H.finite
  projective_quotient := H.projective
  rankAtStalk_eq := H.rank

variable [IsNoetherianRing R] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (w : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1) → R)
variable (i : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1))
variable (hi : ∀ c, w c (i c) = 1)
variable (hw : ∀ c, (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (w c) (i c) (hi c))

include A I e eL hg hδ hN hunit level hD hlarge i hi hw

theorem auxiliaryTorsionConfiguration_evaluation_kernel :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D :=
  Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation_kernel I.ideal I.saturated
    (fun c => A.abelian.fullLevelGlobalSection level c ≫ e.hom.left)
    (Noetherian.TorsionConfigurationDeterminesIdeal.noetherianEmbeddedGraph_sectionsDetectedBy_fullLevel A I.ideal e eL
      hg hδ hN hunit level D D hD le_rfl hlarge) w i hi hw

theorem auxiliaryTorsionConfiguration_hasHilbertRank
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D) :
    HomogeneousConfigurationHasRank w D (P.eval (D : ℚ)).num.toNat := by
  have hk := auxiliaryTorsionConfiguration_evaluation_kernel A I e eL hg hδ hN hunit
    level D hD hlarge w i hi hw
  constructor
  · rw [hk]
    exact HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  · rw [hk]
    exact HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I.ideal I.saturated P I.hilbert D
      ((le_max_left _ _).trans hdegree)
  · intro p
    rw [hk]
    exact HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I.ideal I.saturated P I.hilbert D hdegree p

theorem auxiliaryTorsionConfiguration_grassmannian_eq
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D) :
    homogeneousConfigurationGrassmannian w D (P.eval (D : ℚ)).num.toNat
      (auxiliaryTorsionConfiguration_hasHilbertRank A I e eL hg hδ hN hunit
        level D hD hlarge w i hi hw hdegree) =
      HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformFlatFamilyHilbertGrassmannian I.ideal I.saturated P I.hilbert D hdegree := by
  apply Module.Grassmannian.ext
  exact auxiliaryTorsionConfiguration_evaluation_kernel A I e eL hg hδ hN hunit
    level D hD hlarge w i hi hw

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationEvaluationKernel
