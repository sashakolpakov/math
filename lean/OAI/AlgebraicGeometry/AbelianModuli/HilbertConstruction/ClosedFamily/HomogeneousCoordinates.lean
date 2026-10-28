import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence

/-! # Homogeneous Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every actual flat closed family in projective space has its canonical saturated homogeneous ideal and an actual family isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n))

def Closed.Families.FlatClosedFamily.homogeneousIdeal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf F.ideal

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_saturated : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated F.homogeneousIdeal.toIdeal :=
  HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated F.ideal

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_kernel :
    (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding F.homogeneousIdeal).left.ker = F.inclusion.left.ker := by
  change (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf F.ideal)).ker = F.ideal.subschemeι.ker
  exact (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf F.ideal).trans F.ideal.ker_subschemeι.symm

def Closed.Families.FlatClosedFamily.homogeneousFamilyIso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal ≅ F.scheme :=
  Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding F.homogeneousIdeal) F.inclusion F.homogeneousIdeal_kernel

theorem Closed.Families.FlatClosedFamily.homogeneousIdeal_flat : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading F.homogeneousIdeal)) := by
  let e := F.homogeneousFamilyIso
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : Flat F.scheme.hom := F.flat
  have hh : Flat (e.hom.left ≫ F.scheme.hom) := inferInstance
  change Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily F.homogeneousIdeal).hom
  exact e.hom.w ▸ hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
