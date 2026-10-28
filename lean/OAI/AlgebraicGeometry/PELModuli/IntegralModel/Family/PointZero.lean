import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointEq

/-! # Point Zero -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointZero.FamilyPointTransport

noncomputable section

/-! Transport of the actual zero section in a group family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem over_one_left {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f : T ⟶ S) :
    (1 : Over.mk f ⟶ A).left = f ≫ (MonObj.one : 𝟙_ (Over S) ⟶ A).left := rfl

theorem transport_one {S T : Scheme.{0}} (A : Over S) [GrpObj A] (f g : T ⟶ S)
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) [IsMonHom e.hom] :
    PointBaseChange.FamilyPointTransport.transport A f g e (f ≫ (MonObj.one : 𝟙_ (Over S) ⟶ A).left)
      (by rw [Category.assoc, (MonObj.one : 𝟙_ (Over S) ⟶ A).w]; exact Category.comp_id f) =
      g ≫ (MonObj.one : 𝟙_ (Over S) ⟶ A).left :=
  congrArg Over.Hom.left (PointEq.FamilyPointTransport.transportPoint_one A f g e)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointZero.FamilyPointTransport
