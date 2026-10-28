import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReconstructedProjectiveFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Reconstructed Closed Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Over a noetherian coefficient ring, the reconstructed proper flat projective
scheme gives an actual HilbertConstruction flat finitely presented closed family. Its canonical
ideal-sheaf model is isomorphic to the reconstructed projective quotient.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R σ : Type u} [CommRing R] [IsNoetherianRing R] [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (D : GradedIdealReconstruction.GradedIdealRelations R σ)
variable (h : ∀ d, Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ D.piece d))

instance GradedIdealReconstruction.GradedIdealRelations.projectiveFamily_locallyFinitePresentation : LocallyOfFinitePresentation D.projectiveFamily.hom :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

def GradedIdealReconstruction.GradedIdealRelations.flatClosedFamily : Closed.Families.FlatClosedFamily
    (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (MvPolynomial.homogeneousSubmodule σ R))) := by
  have : Flat D.projectiveFamily.hom := D.projectiveFamily_flat h
  exact Closed.Families.FlatClosedFamily.ofEmbedding D.projectiveFamilyEmbedding

def GradedIdealReconstruction.GradedIdealRelations.flatClosedFamilyIso : D.projectiveFamily ≅ (D.flatClosedFamily h).scheme := by
  have : Flat D.projectiveFamily.hom := D.projectiveFamily_flat h
  exact Closed.Families.FlatClosedFamily.ofEmbeddingIso D.projectiveFamilyEmbedding

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
