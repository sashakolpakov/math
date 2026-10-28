import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components

/-! # Component Presentations -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ComponentPresentations.Components

noncomputable section

/-! Actual integral components inherit the given closed projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom]
  (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom)

def componentProjectivePresentation (C : irreducibleComponents X.left) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (Betti.Smooth.Components.componentOver X C).left (Betti.Smooth.Components.componentOver X C).hom where
  ambientDimension := P.ambientDimension
  embedding := (Betti.Smooth.Components.componentInclusion X C).left ≫ P.embedding
  closedImmersion := inferInstance
  over_base := by
    rw [Category.assoc, P.over_base]
    rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ComponentPresentations.Components
