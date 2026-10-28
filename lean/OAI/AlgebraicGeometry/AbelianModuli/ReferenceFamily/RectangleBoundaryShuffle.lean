import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.BoundaryShuffle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleMixedClassProjection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductComponentRestriction

/-! # Rectangle Boundary Shuffle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleBoundaryShuffle

noncomputable section

/-! The literal four-corner shuffle of an ordinary product-cover
boundary is the difference of its two actual rectangle boundaries.
Consequently its mixed tensor class vanishes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech

variable {k : Type} [Field k] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {I J : Type} (U : I → X.Opens) (V : J → Y.Opens)

abbrev rectangleOrdinaryCech2 := ∀ p q r : Σ _ : I, J,
  Γ(pullback f g, (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V p ⊓ Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V q) ⊓
    Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V r)

def rectangleTripleShuffle (w : rectangleOrdinaryCech2 f g U V) : Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCech11 f g U V :=
  fun i i' j j' =>
    Regular.BoundaryShuffle.regularTripleSectionOn (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) w
      ⟨i, j⟩ ⟨i', j⟩ ⟨i', j'⟩ (Quotients.FiniteDescent.CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j'))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_left))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_left))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_right)) -
    Regular.BoundaryShuffle.regularTripleSectionOn (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) w
      ⟨i, j⟩ ⟨i, j'⟩ ⟨i', j'⟩ (Quotients.FiniteDescent.CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j'))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_left))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_right))
      (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_right))

theorem rectangleTripleShuffle_boundary (v : Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V)
    (w : rectangleOrdinaryCech2 f g U V)
    (hw : Regular.BoundaryShuffle.RegularTripleBoundary (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) v w) :
    rectangleTripleShuffle f g U V w =
      Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD01h f g U V (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V v) -
        Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech.rectangleCechD10v f g U V (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V v) := by
  funext i i' j j'
  let W := Quotients.FiniteDescent.CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j')
  have hA' := Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech.rectangleHorizontalComponent_restrict f g U V v i i' j' W
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i ⊓ U i')) (homOfLE inf_le_right))
  have hA := Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech.rectangleHorizontalComponent_restrict f g U V v i i' j W
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i ⊓ U i')) (homOfLE inf_le_left))
  have hB' := Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech.rectangleVerticalComponent_restrict f g U V v i' j j' W
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j ⊓ V j')))
  have hB := Quotients.FiniteDescent.CubeProductComponentRestriction.Construction.CubeCech.rectangleVerticalComponent_restrict f g U V v i j j' W
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j ⊓ V j')))
  have h := Regular.BoundaryShuffle.regularTripleBoundary_rectangleShuffle (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)
    v w hw ⟨i, j⟩ ⟨i', j⟩ ⟨i', j'⟩ ⟨i, j'⟩ W
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_left))
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_left))
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (homOfLE inf_le_right))
    (Quotients.FiniteDescent.CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (homOfLE inf_le_right))
  exact h.trans (congrArg₂ (· - ·) (congrArg₂ (· - ·) hB'.symm hB.symm)
    (congrArg₂ (· - ·) hA'.symm hA.symm))

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem rectangleTripleShuffle_boundary_class_zero
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i')) (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (v : Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V) (w : rectangleOrdinaryCech2 f g U V)
    (hw : Regular.BoundaryShuffle.RegularTripleBoundary (pullback f g) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) v w) :
    RectangleMixedClassProjection.rectangleMixedClassProjection f g U V hUU hVV (rectangleTripleShuffle f g U V w) = 0 := by
  rw [rectangleTripleShuffle_boundary f g U V v w hw, map_sub]
  have h := RectangleMixedClassProjection.rectangleMixedClassProjection_boundary f g U V hUU hVV hU hV
    (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V v) (Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V v)
  rw [map_sub] at h
  exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RectangleBoundaryShuffle
