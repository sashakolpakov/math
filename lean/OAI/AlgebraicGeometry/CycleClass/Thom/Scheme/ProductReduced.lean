import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs

/-! # Product Reduced -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductReduced.Constructions

noncomputable section

/-! Reducedness of the actual scheme fiber product over the complex base,
proved on the native product of affine covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem schemeProduct_isReduced (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom]
    [AlgebraicGeometry.IsReduced X.left] [AlgebraicGeometry.IsReduced Y.left] :
    AlgebraicGeometry.IsReduced (pullback X.hom Y.hom) := by
  let U := Scheme.Pullback.openCoverOfLeftRight X.left.affineCover Y.left.affineCover X.hom Y.hom
  let : ∀ i, AlgebraicGeometry.IsReduced (U.X i) := by
    rintro ⟨i, j⟩
    let : IsAffine (Over.mk (X.left.affineCover.f i ≫ X.hom)).left := Scheme.isAffine_affineCover X.left i
    let : IsAffine (Over.mk (Y.left.affineCover.f j ≫ Y.hom)).left := Scheme.isAffine_affineCover Y.left j
    let : LocallyOfFiniteType (Over.mk (X.left.affineCover.f i ≫ X.hom)).hom :=
      inferInstanceAs (LocallyOfFiniteType (X.left.affineCover.f i ≫ X.hom))
    let : AlgebraicGeometry.IsReduced (Over.mk (X.left.affineCover.f i ≫ X.hom)).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (X.left.affineCover.X i))
    let : AlgebraicGeometry.IsReduced (Over.mk (Y.left.affineCover.f j ≫ Y.hom)).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Y.left.affineCover.X j))
    exact Affine.ProductIs.Constructions.affineProduct_isReduced
      (Over.mk (X.left.affineCover.f i ≫ X.hom))
      (Over.mk (Y.left.affineCover.f j ≫ Y.hom))
  exact AlgebraicGeometry.IsReduced.of_openCover (pullback X.hom Y.hom) U

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductReduced.Constructions
