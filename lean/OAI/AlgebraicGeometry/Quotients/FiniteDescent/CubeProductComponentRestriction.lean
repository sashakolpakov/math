import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCocycles

/-! # Cube Product Component Restriction -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech

noncomputable section

/-! Restriction formulas for the two components of an ordinary product-cover cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

theorem rectangleHorizontalComponent_restrict (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V)
    (i i' : ι) (j : κ) (W : (pullback f g).Opens)
    (hW : W ≤ CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j)) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.map (homOfLE hW).op
      (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z i i' j) =
      CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 _ (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j⟩ W
        (hW.trans (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j))))
        (hW.trans (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j)))) :=
  CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_comp _ (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j)) W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j)))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j))) hW

theorem rectangleVerticalComponent_restrict (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V)
    (i : ι) (j j' : κ) (W : (pullback f g).Opens)
    (hW : W ≤ CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j')) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.map (homOfLE hW).op
      (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z i j j') =
      CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 _ (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i, j'⟩ W
        (hW.trans (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_left)))
        (hW.trans (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_right))) :=
  CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_comp _ (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i, j'⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j')) W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_left))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_right)) hW

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech
