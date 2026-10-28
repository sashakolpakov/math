import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechSlices
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCechRetractions
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCocycleMixed

/-! # Product Point Cech Kunneth -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductPointCechKunneth.Construction.CubeCech

noncomputable section

/-! A product Cech cocycle is a boundary if its two rational-point slices are boundaries. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

theorem rectangleCech_left_projection_exact_of_slice
    (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _) (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j)
    (a : CubeRectangleCech.Construction.CubeCech.rectangleCech10 f g U V)
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (ha : ∀ i i', CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap f g s hs (U i ⊓ U i') (V j) hj (a i i' j) =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x i i') :
    TensorProduct.map LinearMap.id (CubePointEvaluation.Construction.CubeCech.pointCechRetraction g s hs V j hj)
      ((CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).symm a) =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x ⊗ₜ[k] (1 : k) := by
  apply (TensorProduct.rid k _).injective
  rw [TensorProduct.rid_tmul, one_smul]
  funext i i'
  have h := CubeProductCechSlices.Construction.CubeCech.productCech10_slice f g U V hV hUU s hs j hj
    ((CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU).symm a) i i'
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm.trans (ha i i')

theorem rectangleCech_right_projection_exact_of_slice
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i)
    (b : CubeRectangleCech.Construction.CubeCech.rectangleCech01 f g U V)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (hb : ∀ j j', CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap f g s hs (U i) (V j ⊓ V j') hi (b i j j') =
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y j j') :
    TensorProduct.map (CubePointEvaluation.Construction.CubeCech.pointCechRetraction f s hs U i hi) LinearMap.id
      ((CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).symm b) =
      (1 : k) ⊗ₜ[k] OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y := by
  apply (TensorProduct.lid k _).injective
  rw [TensorProduct.lid_tmul, one_smul]
  funext j j'
  have h := CubeProductCechSlices.Construction.CubeCech.productCech01_slice f g U V hU hVV s hs i hi
    ((CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV).symm b) j j'
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm.trans (hb j j')

include hU hV hUU hVV in
theorem properProductCech_boundary_of_point_slices
    [IsAlgClosed k] [IsIntegral X] [IsIntegral Y] [UniversallyClosed f] [UniversallyClosed g]
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
  obtain ⟨t, htH, htV⟩ := CubeRectangleCechRetractions.Construction.CubeCech.rectangleCech_boundary_of_split_augmentations f g U V hU hV hUU hVV
    (CubePointEvaluation.Construction.CubeCech.pointCechRetraction f sX hsX U i₀ hi₀) (CubePointEvaluation.Construction.CubeCech.pointCechRetraction g sY hsY V j₀ hj₀)
    (CubePointEvaluation.Construction.CubeCech.pointCechRetraction_comp f sX hsX U i₀ hi₀) (CubePointEvaluation.Construction.CubeCech.pointCechRetraction_comp g sY hsY V j₀ hj₀)
    hcoverU hcoverV (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z) (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z)
    (CubeProductCocycleMixed.Construction.CubeCech.rectangleCocycle_mixed f g U V z hz) x y
    (rectangleCech_left_projection_exact_of_slice f g U V hV hUU sY hsY j₀ hj₀ _ x ha)
    (rectangleCech_right_projection_exact_of_slice f g U V hU hVV sX hsX i₀ hi₀ _ y hb)
  exact ⟨fun p ↦ t p.1 p.2, CubeProductCechCocycles.Construction.CubeCech.rectangleCocycle_isBoundary_of_components f g U V z hz t htH htV⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductPointCechKunneth.Construction.CubeCech
