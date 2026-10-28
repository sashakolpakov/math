import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSliceCechMaps
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PointedProductCechBoundary

/-! # Product Axis -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAxis

noncomputable section

/-! Actual structure-sheaf Cech restriction maps to the two rational-point
axes jointly detect boundaries in degree one on a proper integral product. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ProductAxisCechDetection

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)

abbrev source := OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex
  (BaseModule.Construction.BaseModuleSheaf.sheaf (pullback.fst f g ≫ f) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)))
    (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)

def left (s : Spec (.of K) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) :
    source f g U V ⟶ OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) U :=
  StructureCech.Construction.StructureCechPullback.map (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs) (pullback.fst f g ≫ f) f
    (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i => ⟨i, j⟩)
    (fun i => CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj)

def right (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :
    source f g U V ⟶ OpenCechShortComplex.Construction.CubeCech.openModuleCechShortComplex (BaseModule.Construction.BaseModuleSheaf.sheaf g (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) V :=
  StructureCech.Construction.StructureCechPullback.map (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs) (pullback.fst f g ≫ f) g
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs) (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j => ⟨i, j⟩)
    (fun j => CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi)

theorem left_apply (s : Spec (.of K) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) (z : (source f g U V).X₂) :
    (left f g U V s hs j hj).τ₂ z = ProductSliceCechMaps.Construction.CubeCech.productLeftSliceCech1 f g U V s hs j hj z := by
  funext i i'
  exact (StructureCech.Construction.StructureCechPullback.middle_apply (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
    (pullback.fst f g ≫ f) f (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs)
    (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i => ⟨i, j⟩)
    (fun i => CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj) z i i').trans
      (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_apply (pullback.fst f g ≫ f) f (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
        (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs) _ _ _ _).symm

theorem right_apply (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) (z : (source f g U V).X₂) :
    (right f g U V s hs i hi).τ₂ z = ProductSliceCechMaps.Construction.CubeCech.productRightSliceCech1 f g U V s hs i hi z := by
  funext j j'
  exact (StructureCech.Construction.StructureCechPullback.middle_apply (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs)
    (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs)
    (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j => ⟨i, j⟩)
    (fun j => CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi) z j j').trans
      (CubeRelativeSectionsNaturality.Construction.CubeCech.relativeSectionsMap_apply (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs)
        (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs) _ _ _ _).symm

theorem boundary [IsIntegral X] [IsIntegral Y]
    [UniversallyClosed f] [UniversallyClosed g]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (sX : Spec (.of K) ⟶ X) (hsX : sX ≫ f = 𝟙 _)
    (sY : Spec (.of K) ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
    (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)
    (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)
    (z : (source f g U V).X₂) (hz : (source f g U V).g z = 0)
    (hl : (left f g U V sY hsY j₀ hj₀).τ₂ z ∈
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (BaseModule.Construction.BaseModuleSheaf.sheaf f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) U).range)
    (hr : (right f g U V sX hsX i₀ hi₀).τ₂ z ∈
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (BaseModule.Construction.BaseModuleSheaf.sheaf g (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) V).range) :
    z ∈ (source f g U V).f.hom.range := by
  obtain ⟨x, hx⟩ := hl
  obtain ⟨y, hy⟩ := hr
  have hc : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) z :=
    (OpenCechShortComplex.Construction.CubeCech.openModuleCechD1_eq_zero_iff _ _ z).mp hz
  obtain ⟨t, ht⟩ := PointedProductCechBoundary.Construction.CubeCech.properProductCech_boundary_of_rational_axes f g U V hU hV hUU hVV
    sX hsX sY hsY i₀ hi₀ j₀ hj₀ hcoverU hcoverV z hc x y
    (fun i i' => (ProductSliceCechMaps.Construction.CubeCech.productLeftSliceCech1_apply f g U V sY hsY j₀ hj₀ z i i').symm.trans
      (congrFun (congrFun ((left_apply f g U V sY hsY j₀ hj₀ z).symm.trans hx.symm) i) i'))
    (fun j j' => (ProductSliceCechMaps.Construction.CubeCech.productRightSliceCech1_apply f g U V sX hsX i₀ hi₀ z j j').symm.trans
      (congrFun (congrFun ((right_apply f g U V sX hsX i₀ hi₀ z).symm.trans hy.symm) j) j'))
  exact ⟨t, ht⟩

end Construction.ProductAxisCechDetection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAxis
