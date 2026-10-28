import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Derived Base Change -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedBaseChange

noncomputable section

/-! A commuting square of additive functors gives a comparison of left
derived functors when the vertical functors preserve the required exactness
and projective objects. The comparison is constructed from projective
resolutions. -/

open _root_.CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {C' : Type u₃} [Category.{v₃} C'] [Abelian C'] [EnoughProjectives C']
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

def leftDerivedIso (F : C ⥤ D) (F' : C' ⥤ D') (H : C ⥤ C') (G : D ⥤ D')
    [F.Additive] [F'.Additive] [H.Additive] [G.Additive]
    [H.PreservesProjectiveObjects] [H.PreservesHomology] [G.PreservesHomology]
    (e : H ⋙ F' ≅ F ⋙ G) (M : C) (n : ℕ) :
    (F'.leftDerived n).obj (H.obj M) ≅ G.obj ((F.leftDerived n).obj M) := by
  let P := projectiveResolution M
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  refine (H.mapProjectiveResolution P).isoLeftDerivedObj F' n ≪≫ ?_ ≪≫
    G.mapIso (P.isoLeftDerivedObj F n).symm
  refine (HomologicalComplex.homologyFunctor D' (ComplexShape.down ℕ) n).mapIso
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.down ℕ)).app P.complex) ≪≫ ?_
  exact (K.sc n).mapHomologyIso G

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DerivedBaseChange
