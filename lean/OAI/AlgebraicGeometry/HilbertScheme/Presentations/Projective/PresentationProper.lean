import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ConstructionProjectivePresentationComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Presentation Proper -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! The statement's chosen projective presentations imply properness
and the usual locally noetherian property over a locally noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X : Over S}

theorem Has.Core.ProjectivePresentation.proper (B : Has.Core.ProjectivePresentation X) : IsProper X.hom :=
  B.toHilbertConstruction.proper

theorem Has.Core.ProjectivePresentation.locallyOfFiniteType (B : Has.Core.ProjectivePresentation X) :
    LocallyOfFiniteType X.hom := by
  let : IsProper X.hom := B.proper
  infer_instance

theorem Has.Core.ProjectivePresentation.locallyNoetherian [IsLocallyNoetherian S]
    (B : Has.Core.ProjectivePresentation X) : IsLocallyNoetherian X.left := by
  let : LocallyOfFiniteType X.hom := B.locallyOfFiniteType
  exact LocallyOfFiniteType.isLocallyNoetherian X.hom

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
