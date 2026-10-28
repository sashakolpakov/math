import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.HomogeneousFamilyModels
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeProjectiveEquations

/-! # Degree Family Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite list of homogeneous equations of one common degree represents each actual projective family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeProjectiveEquations.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem Closed.Families.FlatClosedFamily.exists_single_degree_equations
    (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) :
    ∃ (m N : ℕ) (g : Fin m → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hg : ∀ j, (g j).IsHomogeneous N),
      (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)).left.ker = F.ideal := by
  obtain ⟨J, hfg, _, _, hk⟩ := F.exists_finite_homogeneous_equations
  obtain ⟨m, N, g, hg, hs⟩ := HilbertScheme.Presentations.SingleDegreeProjectiveEquations.GradedHilbert.finite_single_degree_projective_equations J hfg
  refine ⟨m, N, g, hg, ?_⟩
  change (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)).ker = F.ideal
  rw [← HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf, hs, HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf]
  exact hk

structure Single.DegreeFamilyModels.ProjectiveFamilyEquations (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) where
  count : ℕ
  degree : ℕ
  polynomial : Fin count → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n
  homogeneous : ∀ j, (polynomial j).IsHomogeneous degree
  kernel :
    (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding
      (HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal polynomial degree homogeneous)).left.ker = F.ideal

def Closed.Families.FlatClosedFamily.equations (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)) :
    Single.DegreeFamilyModels.ProjectiveFamilyEquations F := Classical.choice <| by
  obtain ⟨m, N, g, hg, hk⟩ := F.exists_single_degree_equations
  exact ⟨⟨m, N, g, hg, hk⟩⟩

namespace Single.DegreeFamilyModels.ProjectiveFamilyEquations

variable {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)} (E : ProjectiveFamilyEquations F)

def ideal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.polynomial E.degree E.homogeneous

def familyIso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily E.ideal ≅ F.scheme :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding E.ideal) F.inclusion
    (E.kernel.trans F.ideal.ker_subschemeι.symm)

theorem familyIso_embedding : E.familyIso.hom ≫ F.inclusion = Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding E.ideal :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding _ _ _

end Single.DegreeFamilyModels.ProjectiveFamilyEquations

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
