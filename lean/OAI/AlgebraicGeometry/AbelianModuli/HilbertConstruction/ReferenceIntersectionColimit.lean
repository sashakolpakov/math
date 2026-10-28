import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionDirectedCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.Pullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Locally.DirectedPullbackDiagram
import Mathlib.AlgebraicGeometry.Gluing

/-! # Reference Intersection Colimit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionColimit

noncomputable section

/-! The colimit of the original intersection diagram is canonically the original scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

instance originalIntersection_hasColimit :
    HasColimit (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) :=
  ⟨ReferenceIntersectionDirectedCover.originalIntersectionCocone X, ReferenceIntersectionDirectedCover.originalIntersection_isColimit X⟩

instance originalIntersectionScheme_isLocallyDirected :
    ((ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) ⋙ Scheme.forget).IsLocallyDirected := by
  apply Locally.DirectedPullbackDiagram.schemeDiagram_isLocallyDirected_of_pullbacks
  intro T U S hTS hUS
  exact ⟨FiniteIntersection.Unions.finiteIntersectionUnion X T U,
    homOfLE (FiniteIntersection.Unions.finiteIntersection_subset_union_left X T U),
    homOfLE (FiniteIntersection.Unions.finiteIntersection_subset_union_right X T U),
    FiniteIntersection.Pullbacks.finiteIntersection_isPullback X (leOfHom hTS) (leOfHom hUS)⟩

def originalIntersectionColimitIso :
    colimit (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) ≅ X.left :=
  (colimit.isColimit _).coconePointUniqueUpToIso (ReferenceIntersectionDirectedCover.originalIntersection_isColimit X)

theorem originalIntersectionColimitIso_ι (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    colimit.ι (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) S ≫
      (originalIntersectionColimitIso X).hom = (Finite.AffineIntersections.finiteIntersectionOpen X S).ι :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (ReferenceIntersectionDirectedCover.originalIntersection_isColimit X) S

theorem originalIntersectionColimitIso_ι_base (S : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ) :
    colimit.ι (ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))) S ≫
      ((originalIntersectionColimitIso X).hom ≫ X.hom) = (Finite.AffineIntersections.finiteIntersectionChart X S).hom := by
  rw [← Category.assoc, originalIntersectionColimitIso_ι]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionColimit
