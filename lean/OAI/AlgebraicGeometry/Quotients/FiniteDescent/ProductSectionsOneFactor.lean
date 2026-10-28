import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSectionsNaturality

/-! # Product Sections One Factor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSectionsOneFactor.Construction.CubeCech

noncomputable section

/-! Restriction of product-section tensor coordinates in one factor at a time. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

abbrev rectangleSectionRestriction {U U' : X.Opens} {V V' : Y.Opens}
    (i : U' ⟶ U) (j : V' ⟶ V) :=
  ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.map
    (homOfLE (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g i j)).op).hom

theorem productRectangleModuleSectionsEquiv_restrict_left_tmul
    {U U' : X.Opens} (i : U' ⟶ U) (V : Y.Opens)
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hV : IsAffineOpen V)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U))
    (y : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U' V hU' hV
      ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map i.op x ⊗ₜ[k] y) =
      rectangleSectionRestriction f g i (𝟙 V)
        (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y)) := by
  simpa only [TensorProduct.map_tmul, op_id, CategoryTheory.Functor.map_id,
    ModuleCat.id_apply] using
    CubeProductSectionsNaturality.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict f g i (𝟙 V) hU hV hU' hV (x ⊗ₜ[k] y)

theorem productRectangleModuleSectionsEquiv_restrict_right_tmul
    (U : X.Opens) {V V' : Y.Opens} (j : V' ⟶ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U))
    (y : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V' hU hV'
      (x ⊗ₜ[k] (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.map j.op y) =
      rectangleSectionRestriction f g (𝟙 U) j
        (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV (x ⊗ₜ[k] y)) := by
  simpa only [TensorProduct.map_tmul, op_id, CategoryTheory.Functor.map_id,
    ModuleCat.id_apply] using
    CubeProductSectionsNaturality.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict f g (𝟙 U) j hU hV hU hV' (x ⊗ₜ[k] y)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSectionsOneFactor.Construction.CubeCech
