import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.Operations

/-! # Point Section Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionEquivalence

noncomputable section

/-! A point of a family over a test scheme is exactly a unit-domain section of its actual scheme pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (A T : Over S)

def familyPointSectionEquiv : (T ⟶ A) ≃ (𝟙_ (Over T.left) ⟶ (Over.pullback T.hom).obj A) where
  toFun p := Over.homMk
    (pullback.lift p.left (𝟙 T.left) (p.w.trans (Category.id_comp T.hom).symm))
    (pullback.lift_snd _ _ _)
  invFun e := Over.homMk (e.left ≫ pullback.fst A.hom T.hom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (e.left ≫ ((Over.pullback T.hom).obj A).hom) ≫ T.hom = T.hom
    rw [e.w]
    exact Category.id_comp _)
  left_inv p := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv e := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans e.w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionEquivalence
