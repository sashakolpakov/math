import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductComponentRestriction

/-! # Cube Product Cocycle Mixed -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCocycleMixed.Construction.CubeCech

noncomputable section

/-! A Cech cocycle on the rectangle cover satisfies the mixed double-Cech equation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

theorem rectangleCocycle_mixed (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z) :
    CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z) =
      CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z) := by
  funext i i' j j'
  let W := CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j')
  have hA' := CubeProductComponentRestriction.Construction.CubeCech.rectangleHorizontalComponent_restrict f g U V z i i' j' W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i ⊓ U i')) (homOfLE inf_le_right))
  have hA := CubeProductComponentRestriction.Construction.CubeCech.rectangleHorizontalComponent_restrict f g U V z i i' j W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i ⊓ U i')) (homOfLE inf_le_left))
  have hB' := CubeProductComponentRestriction.Construction.CubeCech.rectangleVerticalComponent_restrict f g U V z i' j j' W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j ⊓ V j')))
  have hB := CubeProductComponentRestriction.Construction.CubeCech.rectangleVerticalComponent_restrict f g U V z i j j' W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j ⊓ V j')))
  refine (congrArg₂ (fun a b ↦ a - b) hA' hA).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b ↦ a - b) hB' hB).symm
  exact CubeOpenCechCocycles.Construction.CubeCech.openCechCocycle_square _ _ z hz ⟨i, j⟩ ⟨i', j'⟩ ⟨i', j⟩ ⟨i, j'⟩ W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_left))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_right))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_left))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_right))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCocycleMixed.Construction.CubeCech
