import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSchemeCechPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductRightSlice
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCocycles

/-! # Product Slice Cech Maps -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSliceCechMaps.Construction.CubeCech

noncomputable section

/-! The slice maps on ordinary product-cover cochains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

def productLeftSliceCech0 (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) :=
  CubeSchemeCechPullback.Construction.CubeCech.schemeCechPullback0 (pullback.fst f g ≫ f) f (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
    (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i ↦ ⟨i, j⟩)
    (fun i ↦ CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj)

def productLeftSliceCech1 (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) :=
  CubeSchemeCechPullback.Construction.CubeCech.schemeCechPullback1 (pullback.fst f g ≫ f) f (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
    (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i ↦ ⟨i, j⟩)
    (fun i ↦ CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj)

def productRightSliceCech0 (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :=
  CubeSchemeCechPullback.Construction.CubeCech.schemeCechPullback0 (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs)
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j ↦ ⟨i, j⟩)
    (fun j ↦ CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi)

def productRightSliceCech1 (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :=
  CubeSchemeCechPullback.Construction.CubeCech.schemeCechPullback1 (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs)
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j ↦ ⟨i, j⟩)
    (fun j ↦ CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi)

theorem productLeftSliceCech1_apply (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V) (i i' : ι) :
    productLeftSliceCech1 f g U V s hs j hj z i i' =
      CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap f g s hs (U i ⊓ U i') (V j) hj
        (CubeProductCechCocycles.Construction.CubeCech.rectangleHorizontalComponent f g U V z i i' j) := by
  have he := CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_restrict (pullback.fst f g ≫ f) f (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
    (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs)
    (homOfLE (le_inf
      (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j)))
      (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j)))))
    (𝟙 (U i ⊓ U i'))
    (CubeSchemeCechPullback.Construction.CubeCech.cechPullback_overlap_preimage (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U
      (fun i ↦ ⟨i, j⟩) (fun i ↦ CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj) i i')
    (CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i ⊓ U i') (V j) hj) (z ⟨i, j⟩ ⟨i', j⟩)
  simp only [op_id, CategoryTheory.Functor.map_id, ModuleCat.id_apply] at he
  refine Eq.trans ?_ (he.symm.trans ?_)
  · rfl
  · rfl

theorem productRightSliceCech1_apply (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) (z : CubeProductCechCocycles.Construction.CubeCech.rectangleOrdinaryCech1 f g U V) (j j' : κ) :
    productRightSliceCech1 f g U V s hs i hi z j j' =
      CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap f g s hs (U i) (V j ⊓ V j') hi
        (CubeProductCechCocycles.Construction.CubeCech.rectangleVerticalComponent f g U V z i j j') := by
  have he := CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_restrict (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs)
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs)
    (homOfLE (le_inf
      (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_left))
      (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_right))))
    (𝟙 (V j ⊓ V j'))
    (CubeSchemeCechPullback.Construction.CubeCech.cechPullback_overlap_preimage (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V
      (fun j ↦ ⟨i, j⟩) (fun j ↦ CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi) j j')
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j ⊓ V j') hi) (z ⟨i, j⟩ ⟨i, j'⟩)
  simp only [op_id, CategoryTheory.Functor.map_id, ModuleCat.id_apply] at he
  refine Eq.trans ?_ (he.symm.trans ?_)
  · rfl
  · rfl

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSliceCechMaps.Construction.CubeCech
