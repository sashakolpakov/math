import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductPointCechKunneth
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedGlobalConstants
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ExactRectangleCech

/-! # Pointed Product Cech Boundary -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedProductCechBoundary.Construction.CubeCech

noncomputable section

/-! Rational-point axes detect product Cech boundaries over an arbitrary field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι κ : Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

include hU hV hUU hVV in
theorem properProductCech_boundary_of_rational_axes
    [IsIntegral X] [IsIntegral Y] [UniversallyClosed f] [UniversallyClosed g]
    (sX : Spec (.of k) ⟶ X) (hsX : sX ≫ f = 𝟙 _)
    (sY : Spec (.of k) ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
    (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)
    (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)
    (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z)
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (ha : ∀ i i', CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap f g sY hsY (U i ⊓ U i') (V j₀) hj₀
      (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z i i' j₀) =
        OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x i i')
    (hb : ∀ j j', CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap f g sX hsX (U i₀) (V j ⊓ V j') hi₀
      (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z i₀ j j') =
        OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y j j') :
    ∃ t : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V),
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
        (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) t = z := by
  obtain ⟨t, htH, htV⟩ := ExactRectangleCech.Construction.CubeCech.rectangleCech_boundary_of_exact_augmentations f g U V hU hV hUU hVV
    (PointedGlobalConstants.Construction.CubeCech.properCechAugmentation_exact_of_point f sX hsX U hcoverU)
    (PointedGlobalConstants.Construction.CubeCech.properCechAugmentation_exact_of_point g sY hsY V hcoverV)
    (CubePointEvaluation.Construction.CubeCech.pointCechRetraction f sX hsX U i₀ hi₀) (CubePointEvaluation.Construction.CubeCech.pointCechRetraction g sY hsY V j₀ hj₀)
    (CubePointEvaluation.Construction.CubeCech.pointCechRetraction_comp f sX hsX U i₀ hi₀) (CubePointEvaluation.Construction.CubeCech.pointCechRetraction_comp g sY hsY V j₀ hj₀)
    (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z) (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z)
    (CubeProductCocycleMixed.Construction.CubeCech.rectangleCocycle_mixed f g U V z hz) x y
    (ProductPointCechKunneth.Construction.CubeCech.rectangleCech_left_projection_exact_of_slice f g U V hV hUU sY hsY j₀ hj₀ _ x ha)
    (ProductPointCechKunneth.Construction.CubeCech.rectangleCech_right_projection_exact_of_slice f g U V hU hVV sX hsX i₀ hi₀ _ y hb)
  exact ⟨fun p ↦ t p.1 p.2, CubeProductCechCocycles.Construction.CubeCech.rectangleCocycle_isBoundary_of_components f g U V z hz t htH htV⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedProductCechBoundary.Construction.CubeCech
