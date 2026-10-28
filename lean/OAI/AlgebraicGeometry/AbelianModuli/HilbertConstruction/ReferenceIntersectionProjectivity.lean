import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionColimit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Reference Intersection Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionProjectivity

noncomputable section

/-! The original finite affine intersection gluing is the original scheme over the base, with its projective presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (X : Over (Spec (.of R))) [CompactSpace X.left]

local instance originalIntersectionProjective_open {i j : (Finite.AffineIntersections.finiteIntersectionIndex X)ᵒᵈ} (h : i ⟶ j) :
    IsOpenImmersion ((ReferenceIntersectionFunctor.originalIntersectionFunctor X ⋙ Over.forget (Spec (.of R))).map h) :=
  ReferenceIntersectionFunctor.originalIntersectionFunctor_open X h

def originalIntersectionGluedOverIso :
    Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap (ReferenceIntersectionFunctor.originalIntersectionFunctor X)) ≅ X := by
  refine Over.isoMk (ReferenceIntersectionColimit.originalIntersectionColimitIso X) ?_
  apply colimit.hom_ext
  intro i
  exact (ReferenceIntersectionColimit.originalIntersectionColimitIso_ι_base X i).trans
    (Smooth.DiagramGluing.smoothDiagramGluedMap_ι (ReferenceIntersectionFunctor.originalIntersectionFunctor X) i).symm

def originalIntersectionGluedProjective (P : Projective.ProjectivePresentations.ProjectivePresentation X) :
    Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (Smooth.DiagramGluing.smoothDiagramGluedMap (ReferenceIntersectionFunctor.originalIntersectionFunctor X))) :=
  P.ofSourceIso (originalIntersectionGluedOverIso X)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReferenceIntersectionProjectivity
