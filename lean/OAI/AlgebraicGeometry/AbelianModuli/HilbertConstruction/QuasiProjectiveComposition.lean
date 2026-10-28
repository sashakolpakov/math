import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveCompositeImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Quasi Projective Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Quasi-projective presentations over a noetherian base compose through an actual immersion into a projective product compactification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def Projective.ProjectivePresentations.QuasiProjectivePresentation.composition {S : Scheme.{u}} [IsNoetherian S] {M : Over S} {X : Over M.left}
    (P : Projective.ProjectivePresentations.QuasiProjectivePresentation M) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation ((Over.map M.hom).obj X) := by
  have : IsNoetherian M.left := P.noetherian
  have : IsNoetherian X.left := Q.noetherian
  have : TopologicalSpace.NoetherianSpace ((Over.map M.hom).obj X).left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace X.left)
  have : IsImmersion (QuasiProjectiveCompositeImmersion.quasiProjectiveCompositeEmbedding P Q).left :=
    QuasiProjectiveCompositeImmersion.quasiProjectiveCompositeEmbedding_immersion P Q
  have : QuasiCompact (QuasiProjectiveCompositeImmersion.quasiProjectiveCompositeEmbedding P Q).left := inferInstance
  exact (QuasiProjectiveCompositeImmersion.quasiProjectiveCompositeProjectivePresentation P Q).quasiProjectiveImmersion
    (QuasiProjectiveCompositeImmersion.quasiProjectiveCompositeEmbedding P Q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
