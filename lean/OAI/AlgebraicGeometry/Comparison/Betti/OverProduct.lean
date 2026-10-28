import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Over Product -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OverProduct.RingedModules

noncomputable section

/-! A functor preserving binary products commutes with the right adjoints to open-slice restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type} [SmallCategory C] [SmallCategory D]
  [HasBinaryProducts C] [HasBinaryProducts D] (F : C ⥤ D) (U : C)
  [∀ V, IsIso (prodComparison F U V)]

def overStarPostIso : Over.star U ⋙ Over.post F ≅ F ⋙ Over.star (F.obj U) :=
  NatIso.ofComponents (fun V => by
    let e := asIso (prodComparison F U V)
    refine Over.isoMk e ?_
    change prodComparison F U V ≫ (prod.lift prod.fst (𝟙 (F.obj U ⨯ F.obj V)) ≫ prod.fst) =
      F.map (prod.lift prod.fst (𝟙 (U ⨯ V)) ≫ prod.fst)
    simpa only [prod.lift_fst] using prodComparison_fst F U V) (by
      intro V W f
      apply Over.OverMorphism.ext
      change F.map (prod.map (𝟙 U) f) ≫ prodComparison F U W =
        prodComparison F U V ≫ prod.map (𝟙 (F.obj U)) (F.map f)
      simpa only [Functor.map_id] using prodComparison_natural F (𝟙 U) f)

theorem overStarPostIso_hom_left (V : C) :
    ((overStarPostIso F U).hom.app V).left = prodComparison F U V := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.OverProduct.RingedModules
