import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ComplexComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

/-! # Model Complex Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelComplexComparison

noncomputable section

/-! Exact complex comparisons of arithmetic models preserve diagram
maps and the native group structures supplied by SpreadingOut. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)

def arithmeticModelComplexComparison
    (M : Over B.base) (X : Over (Spec (.of K)))
    (e : (Over.pullback B.generic).obj M ≅ (Over.pullback B.fieldExtension).obj X) :
    (Over.pullback B.complexPoint).obj M ≅ (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X :=
  ((Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.generic (Spec.map (CommRingCat.ofHom B.embedding))
      B.complexPoint rfl).app M).symm ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).mapIso e ≪≫
      (ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B).app X

theorem arithmeticModelComplexComparison_compatible
    {M N : Over B.base} {X Y : Over (Spec (.of K))}
    (eM : (Over.pullback B.generic).obj M ≅ (Over.pullback B.fieldExtension).obj X)
    (eN : (Over.pullback B.generic).obj N ≅ (Over.pullback B.fieldExtension).obj Y)
    (f : M ⟶ N) (g : X ⟶ Y)
    (h : (Over.pullback B.generic).map f ≫ eN.hom = eM.hom ≫ (Over.pullback B.fieldExtension).map g) :
    (Over.pullback B.complexPoint).map f ≫ (arithmeticModelComplexComparison B N Y eN).hom =
      (arithmeticModelComplexComparison B M X eM).hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom κ))).map g := by
  let F := Over.pullback B.generic
  let G := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))
  let H := Over.pullback B.complexPoint
  let J := Over.pullback B.fieldExtension
  let L := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  let c : F ⋙ G ≅ H := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.generic
    (Spec.map (CommRingCat.ofHom B.embedding)) B.complexPoint rfl
  let d : J ⋙ G ≅ L := ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B
  have hc : H.map f ≫ (c.app N).inv = (c.app M).inv ≫ G.map (F.map f) := c.inv.naturality f
  have hd : G.map (J.map g) ≫ (d.app Y).hom = (d.app X).hom ≫ L.map g := d.hom.naturality g
  change H.map f ≫ ((c.app N).inv ≫ G.map eN.hom ≫ (d.app Y).hom) =
    ((c.app M).inv ≫ G.map eM.hom ≫ (d.app X).hom) ≫ L.map g
  calc
    _ = (c.app M).inv ≫ G.map (F.map f ≫ eN.hom) ≫ (d.app Y).hom := by
      rw [G.map_comp, ← Category.assoc (H.map f), hc]
      simp only [Category.assoc]
    _ = (c.app M).inv ≫ G.map (eM.hom ≫ J.map g) ≫ (d.app Y).hom := by rw [h]
    _ = _ := by
      rw [G.map_comp]
      simp only [Category.assoc]
      rw [hd]

theorem arithmeticModelComplexComparison_isMonHom
    (M : Over B.base) (X : Over (Spec (.of K))) [GrpObj M] [GrpObj X]
    (e : (Over.pullback B.generic).obj M ≅ (Over.pullback B.fieldExtension).obj X)
    [IsMonHom e.hom] : IsMonHom (arithmeticModelComplexComparison B M X e).hom := by
  let F := Over.pullback B.generic
  let G := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))
  let H := Over.pullback B.complexPoint
  let J := Over.pullback B.fieldExtension
  let L := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  have he : IsMonHom e.hom := inferInstance
  let : GrpObj (F.obj M) := Functor.grpObjObj (F := F)
  let : GrpObj (J.obj X) := Functor.grpObjObj (F := J)
  let : GrpObj (G.obj (F.obj M)) := Functor.grpObjObj (F := G)
  let : GrpObj (G.obj (J.obj X)) := Functor.grpObjObj (F := G)
  let : IsMonHom e.hom := he
  let c : F ⋙ G ≅ H := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso B.generic
    (Spec.map (CommRingCat.ofHom B.embedding)) B.complexPoint rfl
  let d : J ⋙ G ≅ L := ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B
  let e₁ : G.obj (F.obj M) ≅ H.obj M := c.app M
  let e₂ : G.obj (F.obj M) ≅ G.obj (J.obj X) := G.mapIso e
  let e₃ : G.obj (J.obj X) ≅ L.obj X := d.app X
  have : IsMonHom e₁.hom := Section.Comparisons.iterated_comparison_isMonHom F G H c M
  have : IsMonHom e₂.hom := inferInstanceAs (IsMonHom (G.map e.hom))
  have : IsMonHom e₃.hom := Section.Comparisons.iterated_comparison_isMonHom J G L d X
  change IsMonHom (e₁.inv ≫ e₂.hom ≫ e₃.hom)
  infer_instance

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelComplexComparison
