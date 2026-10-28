import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceOverComposition

/-! # Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Product

noncomputable section

section

/-! Actual maps between base-changed group schemes are maps from
the actual product over the original base via the pullback adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} (T A B : Over S) [GrpObj B]

def pullbackProductTotalIso :
    (Over.map T.hom).obj ((Over.pullback T.hom).obj A) ≅ T ⊗ A :=
  HilbertConstruction.Projective.SpaceOverComposition.overMapPullbackProductIso T A ≪≫ β_ A T

def pullbackProductMorphismEquiv :
    ((Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) ≃ (T ⊗ A ⟶ B) :=
  (GroupDescentIs.GroupBaseChange.baseChangePointsEquiv B T.hom ((Over.pullback T.hom).obj A)).trans
    ((pullbackProductTotalIso T A).homCongr (Iso.refl B))

theorem pullbackProductMorphismEquiv_apply
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    pullbackProductMorphismEquiv T A B f = (pullbackProductTotalIso T A).inv ≫
      GroupDescentIs.GroupBaseChange.baseChangePointsEquiv B T.hom ((Over.pullback T.hom).obj A) f := by
  change _ ≫ _ ≫ 𝟙 B = _
  rw [Category.comp_id]

theorem pullbackProductMorphismEquiv_map (g : A ⟶ B) :
    pullbackProductMorphismEquiv T A B ((Over.pullback T.hom).map g) = snd T A ≫ g := by
  have h : (HilbertConstruction.Projective.SpaceOverComposition.overMapPullbackProductIso T A).inv ≫
      GroupDescentIs.GroupBaseChange.baseChangePointsEquiv B T.hom ((Over.pullback T.hom).obj A)
        ((Over.pullback T.hom).map g) = fst A T ≫ g := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫
      (CategoryTheory.Limits.pullback.lift (CategoryTheory.Limits.pullback.fst A.hom T.hom ≫ g.left)
        (CategoryTheory.Limits.pullback.snd A.hom T.hom) _ ≫ CategoryTheory.Limits.pullback.fst B.hom T.hom) =
      CategoryTheory.Limits.pullback.fst A.hom T.hom ≫ g.left
    rw [Category.id_comp, CategoryTheory.Limits.pullback.lift_fst]
  rw [pullbackProductMorphismEquiv_apply]
  change ((β_ A T).inv ≫ (HilbertConstruction.Projective.SpaceOverComposition.overMapPullbackProductIso T A).inv) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc, braiding_inv_fst]

end

section

/-! The actual total-space comparison has the literal parameter
and fiber projections, and preserves the original scheme maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} (T A : Over S)

theorem pullbackProductTotalIso_inv_first :
    (pullbackProductTotalIso T A).inv.left ≫ pullback.fst A.hom T.hom = (snd T A).left := by
  change ((β_ A T).inv.left ≫ 𝟙 _) ≫ pullback.fst A.hom T.hom = (snd T A).left
  rw [Category.comp_id]
  exact congrArg (fun f => f.left) (braiding_inv_fst A T)

theorem pullbackProductTotalIso_inv_base :
    (pullbackProductTotalIso T A).inv.left ≫ ((Over.pullback T.hom).obj A).hom = (fst T A).left := by
  change ((β_ A T).inv.left ≫ 𝟙 _) ≫ pullback.snd A.hom T.hom = (fst T A).left
  rw [Category.comp_id]
  exact congrArg (fun f => f.left) (braiding_inv_snd A T)

variable (B : Over S) [GrpObj B]

theorem pullbackProductMorphismEquiv_left
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    (pullbackProductMorphismEquiv T A B f).left =
      (pullbackProductTotalIso T A).inv.left ≫ f.left ≫ pullback.fst B.hom T.hom := by
  rw [pullbackProductMorphismEquiv_apply, Over.comp_left, GroupDescentIs.GroupBaseChange.baseChangePointsEquiv_apply]

end

/-! The actual identity section of a base-changed group is the
identity axis in the actual product coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme.{0}} (T A : Over S) [GrpObj A]

theorem pullbackGroupIdentity_fst :
    η[(Over.pullback T.hom).obj A].left ≫ pullback.fst A.hom T.hom = T.hom ≫ η[A].left := by
  have h := congrArg (fun f => f.left)
    ((GroupDescentIs.GroupBaseChange.baseChangePointsMulEquiv A T.hom (𝟙_ (Over T.left))).map_one)
  change (1 : 𝟙_ (Over T.left) ⟶ (Over.pullback T.hom).obj A).left ≫ pullback.fst A.hom T.hom =
    (1 : (Over.map T.hom).obj (𝟙_ (Over T.left)) ⟶ A).left at h
  simp only [Hom.one_def, toUnit_unit, Category.id_comp, Over.comp_left, Over.toUnit_left] at h
  exact h.trans (congrArg (fun f => f ≫ η[A].left) (Category.id_comp T.hom))

theorem pullbackProductTotalIso_identitySection :
    (lift (𝟙 T) (toUnit T ≫ η[A])).left ≫ (pullbackProductTotalIso T A).inv.left =
      η[(Over.pullback T.hom).obj A].left := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackProductTotalIso_inv_first, pullbackGroupIdentity_fst]
    exact congrArg (fun f => f.left) (lift_snd (𝟙 T) (toUnit T ≫ η[A]))
  · change ((lift (𝟙 T) (toUnit T ≫ η[A])).left ≫ (pullbackProductTotalIso T A).inv.left) ≫
        ((Over.pullback T.hom).obj A).hom = η[(Over.pullback T.hom).obj A].left ≫
          ((Over.pullback T.hom).obj A).hom
    rw [Category.assoc, pullbackProductTotalIso_inv_base]
    exact (congrArg (fun f => f.left) (lift_fst (𝟙 T) (toUnit T ≫ η[A]))).trans
      η[(Over.pullback T.hom).obj A].w.symm

variable (B : Over S) [GrpObj B]

theorem pullbackProductMorphismEquiv_identity_ext
    (f g : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (he : η[(Over.pullback T.hom).obj A] ≫ f = η[(Over.pullback T.hom).obj A] ≫ g) :
    lift (𝟙 T) (toUnit T ≫ η[A]) ≫ pullbackProductMorphismEquiv T A B f =
      lift (𝟙 T) (toUnit T ≫ η[A]) ≫ pullbackProductMorphismEquiv T A B g := by
  apply Over.OverMorphism.ext
  change (lift (𝟙 T) (toUnit T ≫ η[A])).left ≫ (pullbackProductMorphismEquiv T A B f).left =
    (lift (𝟙 T) (toUnit T ≫ η[A])).left ≫ (pullbackProductMorphismEquiv T A B g).left
  rw [pullbackProductMorphismEquiv_left, pullbackProductMorphismEquiv_left]
  have h := congrArg (fun h => h.left ≫ pullback.fst B.hom T.hom) he
  simpa only [Over.comp_left, Category.assoc, ← pullbackProductTotalIso_identitySection T A] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Product
