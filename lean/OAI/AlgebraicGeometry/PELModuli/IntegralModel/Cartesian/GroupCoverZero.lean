import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Group Cover Zero -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupCoverZero

noncomputable section

/-! An actual cartesian group comparison makes the quotient cover
preserve the zero section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem cartesian_group_cover_zero {B T : Scheme.{0}} (u : T ⟶ B)
    (G : Over T) [GrpObj G] (A : Over B) [GrpObj A]
    (e : G ≅ (Over.pullback u).obj A) [IsMonHom e.hom]
    (q : G.left ⟶ A.left) (he : e.hom.left ≫ pullback.fst A.hom u = q) :
    (MonObj.one : 𝟙_ (Over T) ⟶ G).left ≫ q = u ≫ (MonObj.one : 𝟙_ (Over B) ⟶ A).left := by
  have hz := congrArg Over.Hom.left ((Family.PointEq.FamilyPointTransport.sectionPointEquiv A u).symm.map_one)
  rw [Family.PointEq.FamilyPointTransport.sectionPointEquiv_symm_left] at hz
  change (MonObj.one : 𝟙_ (Over T) ⟶ (Over.pullback u).obj A).left ≫ pullback.fst A.hom u =
    u ≫ (MonObj.one : 𝟙_ (Over B) ⟶ A).left at hz
  calc
    _ = ((MonObj.one : 𝟙_ (Over T) ⟶ G).left ≫ e.hom.left) ≫ pullback.fst A.hom u := by
      rw [Category.assoc, he]
    _ = (MonObj.one : 𝟙_ (Over T) ⟶ (Over.pullback u).obj A).left ≫ pullback.fst A.hom u :=
      congrArg (fun f => f ≫ pullback.fst A.hom u) (congrArg Over.Hom.left (IsMonHom.one_hom e.hom))
    _ = _ := hz

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.GroupCoverZero
