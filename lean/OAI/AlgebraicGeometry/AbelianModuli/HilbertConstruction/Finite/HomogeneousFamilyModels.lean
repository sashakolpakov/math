import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.FiniteEquations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations

/-! # Homogeneous Family Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite homogeneous models of actual closed projective families over arbitrary rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_locallyFinitePresentation :
    LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) := by
  let e := F.homogeneousFamilyIso
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  have hh : LocallyOfFinitePresentation (e.hom.left ≫ F.scheme.hom) := inferInstance
  change LocallyOfFinitePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal).hom
  exact e.hom.w ▸ hh

theorem Closed.Families.FlatClosedFamily.exists_finite_homogeneous_equations :
    ∃ J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧ J ≤ F.homogeneousIdeal ∧
      HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J = F.homogeneousIdeal ∧
      (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J).left.ker = F.ideal := by
  let : LocallyOfFinitePresentation
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) :=
    F.homogeneousIdeal_locallyFinitePresentation
  obtain ⟨J, hfg, hle, hs⟩ := HilbertScheme.Presentations.Finite.ProjectiveFamilyEquations.GradedHilbert.finite_homogeneous_saturated_equations
    F.homogeneousIdeal F.homogeneousIdeal_saturated
  refine ⟨J, hfg, hle, hs, ?_⟩
  change (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J).ker = F.ideal
  rw [← HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf J, hs]
  exact HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf F.ideal

theorem Closed.Families.FlatClosedFamily.exists_finite_homogeneous_model :
    ∃ J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧
      (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J).left.ker = F.ideal ∧
      Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)) ∧
      LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)) := by
  obtain ⟨J, hfg, _, _, hk⟩ := F.exists_finite_homogeneous_equations
  let e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J ≅ F.scheme :=
    Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J) F.inclusion
      (hk.trans F.ideal.ker_subschemeι.symm)
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : Flat F.scheme.hom := F.flat
  have : LocallyOfFinitePresentation F.scheme.hom := F.locallyFinitePresentation
  have hf : Flat (e.hom.left ≫ F.scheme.hom) := inferInstance
  have hp : LocallyOfFinitePresentation (e.hom.left ≫ F.scheme.hom) := inferInstance
  refine ⟨J, hfg, hk, ?_, ?_⟩
  · change Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J).hom
    exact e.hom.w ▸ hf
  · change LocallyOfFinitePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J).hom
    exact e.hom.w ▸ hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
