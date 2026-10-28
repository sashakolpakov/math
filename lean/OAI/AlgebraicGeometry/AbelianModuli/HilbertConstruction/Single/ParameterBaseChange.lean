import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.BaseChangeMap

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterBaseChange

noncomputable section

/-! Each original family has a specified geometric Cartesian comparison across parameter maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T M : Over S} (f : T ⟶ M) (A : Over S)

theorem parameterFamily_composite_isPullback :
    IsPullback (pullback.fst A.hom T.hom) ((Over.pullback T.hom).obj A).hom A.hom (f.left ≫ M.hom) := by
  rw [f.w]
  exact IsPullback.of_hasPullback A.hom T.hom

def singleParameterBaseChangeMap : ((Over.pullback T.hom).obj A).left ⟶ ((Over.pullback M.hom).obj A).left :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap f.left M.hom (pullback.fst A.hom T.hom) (pullback.fst A.hom M.hom)
    (parameterFamily_composite_isPullback f A) (IsPullback.of_hasPullback A.hom M.hom)

theorem singleParameterBaseChangeMap_comp :
    singleParameterBaseChangeMap f A ≫ pullback.fst A.hom M.hom = pullback.fst A.hom T.hom :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap_comp f.left M.hom _ _
    (parameterFamily_composite_isPullback f A) (IsPullback.of_hasPullback A.hom M.hom)

theorem singleParameterBaseChangeMap_isPullback :
    IsPullback (singleParameterBaseChangeMap f A) ((Over.pullback T.hom).obj A).hom
      ((Over.pullback M.hom).obj A).hom f.left :=
  Cartesian.BaseChangeMap.cartesianBaseChangeMap_isPullback f.left M.hom _ _
    (parameterFamily_composite_isPullback f A) (IsPullback.of_hasPullback A.hom M.hom)

def singleParameterBaseChangeIso : (Over.pullback T.hom).obj A ≅
    (Over.pullback f.left).obj ((Over.pullback M.hom).obj A) :=
  Cartesian.BaseChangeMap.cartesianBaseChangeOverIso f.left M.hom _ _
    (parameterFamily_composite_isPullback f A) (IsPullback.of_hasPullback A.hom M.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterBaseChange
