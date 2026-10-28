import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointBaseChange

/-! # Point Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointProjection.FamilyPointTransport

noncomputable section

/-! Point transport preserves every projection compatible with the
two pulled-back family projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem transport_projection {S T D : Scheme.{0}} (A : Over S) (f g : T ⟶ S)
    (e : (Over.pullback f).obj A ≅ (Over.pullback g).obj A) (r : A.left ⟶ D)
    (he : e.hom.left ≫ pullback.fst A.hom g ≫ r = pullback.fst A.hom f ≫ r)
    (x : T ⟶ A.left) (hx : x ≫ A.hom = f) :
    PointBaseChange.FamilyPointTransport.transport A f g e x hx ≫ r = x ≫ r := by
  change (PointBaseChange.FamilyPointTransport.liftPoint A f x hx ≫ e.hom.left ≫ pullback.fst A.hom g) ≫ r = _
  rw [Category.assoc, Category.assoc, he, ← Category.assoc, PointBaseChange.FamilyPointTransport.liftPoint_fst]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Family.PointProjection.FamilyPointTransport
