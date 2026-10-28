import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyNaturality

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterBaseChange

noncomputable section

/-! Products of the original families over two parameter schemes are related by a specified geometric Cartesian base-change map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A B : Over S)

abbrev parameterProductFamily (T : Over S) : Over T.left :=
  (Over.pullback T.hom).obj A ⊗ (Over.pullback T.hom).obj B

theorem parameterProductFamily_composite_isPullback :
    IsPullback (Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B) (parameterProductFamily A B T).hom
      (A ⊗ B).hom (f.left ≫ M.hom) := by
  rw [f.w]
  exact Graph.FamilyNaturality.overProductBaseChange_isPullback T.hom A B

def productParameterBaseChangeMap : (parameterProductFamily A B T).left ⟶ (parameterProductFamily A B M).left :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap f.left M.hom (Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B) (Graph.FamilyNaturality.overProductBaseChangeMap M.hom A B)
    (parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)

theorem productParameterBaseChangeMap_comp :
    productParameterBaseChangeMap f A B ≫ Graph.FamilyNaturality.overProductBaseChangeMap M.hom A B = Graph.FamilyNaturality.overProductBaseChangeMap T.hom A B :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap_comp f.left M.hom _ _
    (parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)

theorem productParameterBaseChangeMap_over :
    productParameterBaseChangeMap f A B ≫ (parameterProductFamily A B M).hom =
      (parameterProductFamily A B T).hom ≫ f.left :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap_over f.left M.hom _ _
    (parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)

theorem productParameterBaseChangeMap_isPullback :
    IsPullback (productParameterBaseChangeMap f A B) (parameterProductFamily A B T).hom
      (parameterProductFamily A B M).hom f.left :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap_isPullback f.left M.hom _ _
    (parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)

def productParameterBaseChangeIso : parameterProductFamily A B T ≅ (Over.pullback f.left).obj (parameterProductFamily A B M) :=
  Cartesian.BaseChangeMap.cartesianBaseChangeOverIso f.left M.hom _ _
    (parameterProductFamily_composite_isPullback f A B) (Graph.FamilyNaturality.overProductBaseChange_isPullback M.hom A B)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterBaseChange
