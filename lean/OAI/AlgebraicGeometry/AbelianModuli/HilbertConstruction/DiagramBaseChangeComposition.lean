import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Diagram Base Change Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramBaseChangeComposition

noncomputable section

/-! Iterated base change of a diagram agrees naturally with base change along the composite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w u' v'

def diagramBaseChangeCompIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : Type u'} [Category.{v'} J] {X Y Z : C} (F : J ⥤ Over Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h) :
    (F ⋙ Over.pullback g) ⋙ Over.pullback f ≅ F ⋙ Over.pullback h :=
  Functor.associator F (Over.pullback g) (Over.pullback f) ≪≫
    Functor.isoWhiskerLeft F ((Over.pullbackComp f g).symm ≪≫
      eqToIso (congrArg (fun k : X ⟶ Z => Over.pullback k) hw))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DiagramBaseChangeComposition
