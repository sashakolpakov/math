import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Ideal Closed Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Saturated flat Hilbert ideals define actual flat finitely presented closed families in projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {P : Polynomial ℚ}
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P)

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.family_locallyFinitePresentation : LocallyOfFinitePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := by
  have : IsProper (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper I.ideal
  exact LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedFamily : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n) := by
  have : Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := I.flat
  have : LocallyOfFinitePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := I.family_locallyFinitePresentation
  exact Closed.Families.FlatClosedFamily.ofEmbedding (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I.ideal)

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedFamily_ideal : I.closedFamily.ideal = (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal).ker := rfl

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.closedFamilyIso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅ I.closedFamily.scheme := by
  have : Flat (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := I.flat
  have : LocallyOfFinitePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).hom := I.family_locallyFinitePresentation
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I.ideal)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
