import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Projective Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every open subscheme of a projectively presented scheme over a
Noetherian base has an actual quasi-projective presentation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def Projective.ProjectivePresentations.ProjectivePresentation.openQuasiProjective {S : Scheme.{u}} [IsNoetherian S]
    {X : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X) (U : X.left.Opens) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk (U.ι ≫ X.hom)) := by
  letI : IsProper X.hom := P.proper
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  exact {
    locallyFiniteType := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
    quasiCompact := inferInstanceAs (QuasiCompact (U.ι ≫ X.hom))
    compactification := X
    projective := P
    embedding := Over.homMk U.ι rfl
    openImmersion := inferInstanceAs (IsOpenImmersion U.ι) }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
