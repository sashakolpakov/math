import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting

/-! # Presentation Section Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery

noncomputable section

/-! An equality of the original embedded families recovers the line
bundle of the specified section presentation after base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private def rawSectionTwistingIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (O : Z.Modules) (h : f ≫ j = i) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback j).obj O) ≅
      (Scheme.Modules.pullback i).obj O :=
  (Scheme.Modules.pullbackComp f j).app O ≪≫
    (Scheme.Modules.pullbackCongr h).app O

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.baseChangeSectionRecovery
    {B S : Scheme.{u}} {Y : Over B} {X : Over S}
    (P : ProjectivePresentations.ProjectivePresentation Y) (Q : ProjectivePresentations.ProjectivePresentation X)
    (L : Line.Bundles.LineBundle X.left) (D : Q.SectionData L)
    (c : S ⟶ B) (e : X ≅ (Over.pullback c).obj Y)
    (hn : P.dimension = Q.dimension)
    (h : HEq (e.hom.left ≫ (P.baseChange c).embedding.left) Q.embedding.left) :
    ((P.baseChange c).ampleLineBundle.pullback e.hom.left).sheaf ≅ L.sheaf := by
  rcases P with ⟨n, j, hj⟩
  rcases Q with ⟨m, i, hi⟩
  cases hn
  let P : ProjectivePresentations.ProjectivePresentation Y := ⟨n, j, hj⟩
  exact rawSectionTwistingIso e.hom.left i.left (P.baseChange c).embedding.left
    (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf (eq_of_heq h) ≪≫ D.twistingIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery
