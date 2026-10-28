import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationCokernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationEvaluationKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.MonomialMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ProjectiveQuotientRank

/-! # Torsion Evaluation Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationRank

noncomputable section

/-! The exact monomial evaluation matrix of a normalized high-torsion
configuration has flat cokernel of rank label-count minus Hilbert rank
over every noetherian local ring, including nonreduced local rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
variable (e : A.abelian.scheme ≅ HilbertConstruction.Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
variable (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
  (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
variable (hg : 0 < g) (hδ : ∀ j, 0 < δ j) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
variable (level : A.abelian.FullLevel n) (D : ℕ) (hD : 0 < D)
variable (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
variable (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
variable (w : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1) → R)
variable (i : Multiplicative (Fin (2 * g) → ZMod n) → Fin (r + 1)) (hi : ∀ c, w c (i c) = 1)
variable (hw : ∀ c, (A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (w c) (i c) (hi c))

include A I e eL hg hδ hN hunit level hD hdegree hlarge i hi hw

theorem localAuxiliaryTorsionEvaluation_flatRank :
    Module.Flat R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).range) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
      ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸ (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).range) p +
        (P.eval (D : ℚ)).num.toNat = n ^ (2 * g) := by
  let F := Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D
  have hk : F.ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D :=
    TorsionConfigurationEvaluationKernel.auxiliaryTorsionConfiguration_evaluation_kernel A I e eL hg hδ hN hunit
      level D hD hlarge w i hi hw
  have : Module.Projective R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) :=
    HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I.ideal I.saturated P I.hilbert D
      ((le_max_left _ _).trans hdegree)
  have : Module.Free R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) := Module.free_of_flat_of_isLocalRing
  have hQ : Module.finrank R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) = (P.eval (D : ℚ)).num.toNat := by
    have h := HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I.ideal I.saturated P I.hilbert
      D hdegree (IsLocalRing.closedPoint R)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at h
  have hr : Module.finrank R F.range = (P.eval (D : ℚ)).num.toNat := by
    calc
      _ = Module.finrank R ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r D) ⧸ F.ker) := F.quotKerEquivRange.finrank_eq.symm
      _ = Module.finrank R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal D) := by rw [hk]
      _ = _ := hQ
  have : Module.Projective R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸ F.range) :=
    TorsionEvaluationCokernel.localAuxiliaryTorsionEvaluation_projective_cokernel A I e eL hg hδ hN hunit
      level D hD ((le_max_left _ _).trans hdegree) hlarge w i hi hw
  have : Module.Free R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸ F.range) :=
    Module.free_of_flat_of_isLocalRing
  have hfin : Module.finrank R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸ F.range) +
      (P.eval (D : ℚ)).num.toNat = n ^ (2 * g) := by
    have h := ProjectiveQuotientRank.localProjectiveQuotient_finrank_add F.range
    rw [hr, Module.finrank_fintype_fun_eq_card] at h
    simpa using h
  refine ⟨inferInstance, fun p => ?_⟩
  rw [Module.rankAtStalk_eq_finrank_of_free]
  exact hfin

theorem localAuxiliaryTorsionMonomialMatrix_flatRank :
    Module.Flat R ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) ∧
    ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R)
      ((Multiplicative (Fin (2 * g) → ZMod n) → R) ⧸ (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix w D)).range) p +
        (P.eval (D : ℚ)).num.toNat = n ^ (2 * g) := by
  rw [Configuration.MonomialMatrix.configurationMonomialMatrix_range]
  exact localAuxiliaryTorsionEvaluation_flatRank A I e eL hg hδ hN hunit
      level D hD hdegree hlarge w i hi hw

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionEvaluationRank
