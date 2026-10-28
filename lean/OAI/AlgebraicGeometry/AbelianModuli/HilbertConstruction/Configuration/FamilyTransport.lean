import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdealProjectiveIso
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyTransport

noncomputable section

/-! Matching configuration relation kernels determine the
coordinate-transformed Hilbert ideal exactly. Consequently the
canonical ambient projective transport restricts to a unique actual
isomorphism of the two flat projective families. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {P : Polynomial ℚ} {ι : Type v}
variable (I J : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P)
variable (v w : ι → Fin (n + 1) → R) (D : ℕ)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (hI : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation v D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal D)
variable (hJ : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w D).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations J.ideal.toIdeal D)

include hD hI hJ

theorem configuration_frame_recovers_hilbertIdeal
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (h : ∀ z, w z = (s z : R) • T (v z)) :
    J = I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T) := by
  have hw : w = fun z j => (s z : R) * T (v z) j :=
    funext (fun z => funext (fun j => congrFun (h z) j))
  have hker := I.coordinateChange_configuration_kernel v D T s hI
  rw [← hw] at hker
  apply SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.ext
  exact HilbertScheme.Presentations.Uniform.FamilyReconstruction.GradedHilbert.uniformFamily_eq_of_degreeRelations_eq J.ideal J.saturated P J.hilbert
    (I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T)).ideal
    (I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T)).saturated
    (I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T)).hilbert D hD (hJ.symm.trans hker)

theorem configurationHilbertFamilyIso_exists
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (h : ∀ z, w z = (s z : R) • T (v z)) :
    ∃ e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J.ideal,
      e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal =
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ (PointCoordinateProjectiveAction.pointCoordinateProjectiveIso T).hom.left := by
  have he := configuration_frame_recovers_hilbertIdeal I J v w D hD hI hJ T s h
  subst J
  exact ⟨Linear.CoordinateIdealProjectiveIso.linearCoordinateIdealFamilyIso (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T) I.ideal,
    Linear.CoordinateIdealProjectiveIso.linearCoordinateIdealProjectiveIso_ambient (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T) I.ideal⟩

theorem configurationHilbertFamilyTransport_existsUnique (h : ProjectiveTransport.ConfigurationFrameRelated v w) :
    ∃! e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J.ideal,
      e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal =
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ (ProjectiveTransport.configurationProjectiveTransport v w h).hom.left := by
  obtain ⟨e, he⟩ := configurationHilbertFamilyIso_exists I J v w D hD hI hJ
    h.choose h.choose_spec.choose h.choose_spec.choose_spec
  refine ⟨e, he, fun f hf => ?_⟩
  apply Iso.ext
  apply Over.OverMorphism.ext
  exact (cancel_mono (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal)).mp (hf.trans he.symm)

def configurationHilbertFamilyTransport (h : ProjectiveTransport.ConfigurationFrameRelated v w) :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J.ideal :=
  (configurationHilbertFamilyTransport_existsUnique I J v w D hD hI hJ h).choose

theorem configurationHilbertFamilyTransport_ambient (h : ProjectiveTransport.ConfigurationFrameRelated v w) :
    (configurationHilbertFamilyTransport I J v w D hD hI hJ h).hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ (ProjectiveTransport.configurationProjectiveTransport v w h).hom.left :=
  (configurationHilbertFamilyTransport_existsUnique I J v w D hD hI hJ h).choose_spec.1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FamilyTransport
