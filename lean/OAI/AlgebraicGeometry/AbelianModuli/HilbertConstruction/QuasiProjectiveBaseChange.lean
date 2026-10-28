import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Quasi Projective Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual quasi-projective presentations persist under arbitrary scheme base change. The projective compactification and its open embedding are both pulled back. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def Projective.ProjectivePresentations.QuasiProjectivePresentation.baseChange
    {S T : Scheme.{u}} {X : Over S} (P : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (f : T ⟶ S) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation ((Over.pullback f).obj X) := by
  have : LocallyOfFiniteType X.hom := P.locallyFiniteType
  have : QuasiCompact X.hom := P.quasiCompact
  exact
    { locallyFiniteType := inferInstanceAs (LocallyOfFiniteType (pullback.snd X.hom f))
      quasiCompact := inferInstanceAs (QuasiCompact (pullback.snd X.hom f))
      compactification := (Over.pullback f).obj P.compactification
      projective := P.projective.baseChange f
      embedding := (Over.pullback f).map P.embedding
      openImmersion := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (Projective.PresentationBaseChange.overPullback_map_isPullback P.embedding f) P.openImmersion }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
