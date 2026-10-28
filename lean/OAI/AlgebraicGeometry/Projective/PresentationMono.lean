import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Presentation Mono -/

namespace OAI.AlgebraicGeometry.Projective.PresentationMono.HilbertConstruction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
theorem projectivePresentationEmbeddingMono {S : Scheme.{u}} {X : Over S}
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) : Mono P.embedding.left := by
  let : IsClosedImmersion P.embedding.left := P.closedImmersion
  infer_instance

end

end OAI.AlgebraicGeometry.Projective.PresentationMono.HilbertConstruction
