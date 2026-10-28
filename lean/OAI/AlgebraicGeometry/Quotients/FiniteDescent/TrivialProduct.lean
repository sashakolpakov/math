import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductAxis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleCechAxis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBoundary

/-! # Trivial Product -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialProduct

noncomputable section

/-! The two axes detect first Cech cohomology for any trivial line bundle
on a proper integral product, with arbitrary trivializations on the axes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.TrivialProductAxisDetection

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    {ι κ : Type u} (U : ι → X.Opens) (V : κ → Y.Opens)
    (M : (pullback f g).Modules)

abbrev source := (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor (pullback.fst f g ≫ f)
  (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)).obj M

def left (s : Spec (.of K) ⟶ Y) (hs : s ≫ g = 𝟙 _)
    (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j) :=
  ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs) (pullback.fst f g ≫ f) f
    (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g s hs) M (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i => ⟨i, j⟩)
    (fun i => CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs (U i) (V j) hj)

def right (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i) :=
  ModuleCechPullbackShort.Construction.ModuleCechPullback.shortMap (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g s hs) (pullback.fst f g ≫ f) g
    (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g s hs) M (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j => ⟨i, j⟩)
    (fun j => CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g s hs (U i) (V j) hi)

theorem jointly [IsIntegral X] [IsIntegral Y]
    [UniversallyClosed f] [UniversallyClosed g]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))
    (sX : Spec (.of K) ⟶ X) (hsX : sX ≫ f = 𝟙 _)
    (sY : Spec (.of K) ⟶ Y) (hsY : sY ≫ g = 𝟙 _)
    (i₀ : ι) (hi₀ : ⊤ ≤ sX ⁻¹ᵁ U i₀) (j₀ : κ) (hj₀ : ⊤ ≤ sY ⁻¹ᵁ V j₀)
    (hcoverU : iSup U = ⊤) (hcoverV : iSup V = ⊤)
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (pullback f g)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      (left f g U V M sY hsY j₀ hj₀) (right f g U V M sX hsX i₀ hi₀) := by
  let E := (CechCoefficient.Construction.CechCoefficientFunctor.moduleFunctor (pullback.fst f g ≫ f)
    (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V)).mapIso e
  let A := ModuleCechAxis.Construction.ModuleCechNormalization.axisIso (CubeProductSlices.Construction.CubeCech.productSliceLeft f g sY hsY) f e U
  let B := ModuleCechAxis.Construction.ModuleCechNormalization.axisIso (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g sX hsX) g e V
  apply CechBoundary.Construction.CechBoundaryTransport.jointly_of_iso
    (left f g U V M sY hsY j₀ hj₀) (right f g U V M sX hsX i₀ hi₀)
    (ProductAxis.Construction.ProductAxisCechDetection.left f g U V sY hsY j₀ hj₀)
    (ProductAxis.Construction.ProductAxisCechDetection.right f g U V sX hsX i₀ hi₀) E A.hom B.hom
  · exact ModuleCechAxis.Construction.ModuleCechNormalization.square (CubeProductSlices.Construction.CubeCech.productSliceLeft f g sY hsY)
      (pullback.fst f g ≫ f) f (CubeProductSliceLinear.Construction.CubeCech.productSliceLeft_over f g sY hsY) e
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) U (fun i => ⟨i, j₀⟩)
      (fun i => CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g sY hsY (U i) (V j₀) hj₀)
  · exact ModuleCechAxis.Construction.ModuleCechNormalization.square (CubeProductRightSlice.Construction.CubeCech.productSliceRight f g sX hsX)
      (pullback.fst f g ≫ f) g (CubeProductRightSlice.Construction.CubeCech.productSliceRight_over f g sX hsX) e
      (CubeProductCechCocycles.Construction.CubeCech.rectangleOpenCover f g U V) V (fun j => ⟨i₀, j⟩)
      (fun j => CubeProductRightSlice.Construction.CubeCech.productSliceRight_rectangle_preimage f g sX hsX (U i₀) (V j) hi₀)
  · exact ProductAxis.Construction.ProductAxisCechDetection.boundary f g U V hU hV hUU hVV
      sX hsX sY hsY i₀ hi₀ j₀ hj₀ hcoverU hcoverV

end Construction.TrivialProductAxisDetection

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TrivialProduct
