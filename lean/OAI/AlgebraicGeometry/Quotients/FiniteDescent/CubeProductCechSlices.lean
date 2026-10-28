import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductRightSlice
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechOverlaps

/-! # Cube Product Cech Slices -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechSlices.Construction.CubeCech

noncomputable section

/-! Rational-point slices in the tensor coordinates of a finite product cover. -/

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

theorem productCech10_slice
    (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _) (j : κ) (hj : ⊤ ≤ s ⁻¹ᵁ V j)
    (a : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i i' : ι) :
    CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap f g s hs (U i ⊓ U i') (V j) hj
      (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU a i i' j) =
    (TensorProduct.rid k _
      (TensorProduct.map LinearMap.id (CubePointEvaluation.Construction.CubeCech.pointCechRetraction g s hs V j hj) a)) i i' := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | tmul x y =>
    have he := (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv_tmul f g U V hV hUU x y i i' j).trans
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i ⊓ U i') (V j)
        (hUU i i') (hV j) (x i i') (y j)).symm
    refine (congrArg (CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap f g s hs (U i ⊓ U i') (V j) hj) he).trans ?_
    exact CubeProductSliceLinear.Construction.CubeCech.productSliceLeftLinearMap_tensor f g s hs (U i ⊓ U i') (V j)
      (hUU i i') (hV j) hj (x i i' ⊗ₜ[k] y j)

theorem productCech01_slice
    (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (i : ι) (hi : ⊤ ≤ s ⁻¹ᵁ U i)
    (b : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (j j' : κ) :
    CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap f g s hs (U i) (V j ⊓ V j') hi
      (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV b i j j') =
    (TensorProduct.lid k _
      (TensorProduct.map (CubePointEvaluation.Construction.CubeCech.pointCechRetraction f s hs U i hi) LinearMap.id b)) j j' := by
  induction b using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  | tmul x y =>
    have he := (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv_tmul f g U V hU hVV x y i j j').trans
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i) (V j ⊓ V j')
        (hU i) (hVV j j') (x i) (y j j')).symm
    refine (congrArg (CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap f g s hs (U i) (V j ⊓ V j') hi) he).trans ?_
    exact CubeProductRightSlice.Construction.CubeCech.productSliceRightLinearMap_tensor f g s hs (U i) (V j ⊓ V j')
      (hU i) (hVV j j') hi (x i ⊗ₜ[k] y j j')

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechSlices.Construction.CubeCech
