import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationEvaluationKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.EvaluationInvariance
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateGrassmannian

/-! # Coordinate Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CoordinateRelations

noncomputable section

/-! The monomial matrix kernel is the actual homogeneous relation
module in fixed coordinates. For auxiliary torsion it therefore gives
the canonical Hilbert Grassmannian point, including over nilpotents. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateGrassmannian.GradedHilbert
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r D : ℕ}

theorem configurationMonomialMatrix_kernel {ι : Type v} [Fintype ι] [DecidableEq ι]
    (w : ι → Fin (r + 1) → R) (D : ℕ) :
    (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w D)).ker =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker.map (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R r D).equivFun.toLinearMap := by
  rw [MonomialMatrix.configurationMonomialMatrix, Homogeneous.ConfigurationEvaluation.homogeneousConfigurationMatrix_linearMap,
    LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm]
  rfl

theorem configurationMonomialMatrix_kernel_relabel
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (w : ι → Fin (r + 1) → R) (D : ℕ) (e : κ ≃ ι) :
    (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix (fun c => w (e c)) D)).ker =
      (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w D)).ker := by
  rw [configurationMonomialMatrix_kernel, configurationMonomialMatrix_kernel,
    EvaluationInvariance.homogeneousConfigurationEvaluation_kernel_relabel]

variable [IsNoetherianRing R] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ j, 0 < δ j) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (w : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1) → R)
variable (i : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1)) (hi : ∀ c, w c (i c) = 1)
variable (hw : ∀ c, (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (w c) (i c) (hi c))

include A I e eL hg hδ hN hunit level hD hlarge i hi hw

theorem auxiliaryTorsionConfiguration_coordinate_kernel :
    (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w D)).ker = HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D := by
  rw [configurationMonomialMatrix_kernel,
    TorsionConfigurationEvaluationKernel.auxiliaryTorsionConfiguration_evaluation_kernel A I e eL hg hδ hN hunit level D hD hlarge w i hi hw]
  rfl

theorem auxiliaryTorsionConfiguration_coordinate_grassmannian
    [Module.Projective R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D)] {k : ℕ}
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) p = k)
    (Q : Module.Grassmannian R (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} r D → R) k)
    (hQ : Q.toSubmodule = (Matrix.toLin' (MonomialMatrix.configurationMonomialMatrix w D)).ker) :
    Q = HilbertScheme.Presentations.DegreeCoordinateGrassmannian.GradedHilbert.degreeCoordinateGrassmannian I.ideal hr := by
  apply Module.Grassmannian.ext
  exact hQ.trans (auxiliaryTorsionConfiguration_coordinate_kernel A I e eL
    hg hδ hN hunit level D hD hlarge w i hi hw)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.CoordinateRelations
