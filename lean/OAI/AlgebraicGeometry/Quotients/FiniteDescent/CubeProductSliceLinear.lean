import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSlices
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeSectionsPullback
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Cube Product Slice Linear -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSliceLinear.Construction.CubeCech

noncomputable section

/-! Rational-point slice restriction is the tensor projection defined by point evaluation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (s : Spec (.of k) ⟶ Y) (hs : s ≫ g = 𝟙 _)

theorem productSliceLeft_over : CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs ≫ (pullback.fst f g ≫ f) = f := by
  rw [← Category.assoc, CubeProductSlices.Construction.CubeCech.productSliceLeft_fst, Category.id_comp]

def productSliceLeftLinearMap (U : X.Opens) (V : Y.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V) :
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g U V)) →ₗ[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) :=
  (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr (productSliceLeft_over f g s hs) U).toLinearMap.comp
    (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback (pullback.fst f g ≫ f) (CubeProductSlices.Construction.CubeCech.productSliceLeft f g s hs)
      (CubeProductSections.Construction.CubeCech.productRectangle f g U V) U (CubeProductSlices.Construction.CubeCech.productSliceLeft_rectangle_preimage f g s hs U V hV))

theorem productSliceLeftLinearMap_apply (U : X.Opens) (V : Y.Opens) (hV : ⊤ ≤ s ⁻¹ᵁ V)
    (x : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g U V))) :
    (productSliceLeftLinearMap f g s hs U V hV x : Γ(X, U)) =
      CubeProductSlices.Construction.CubeCech.productSliceLeftSectionMap f g s hs U V hV x := by
  exact (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsCongr_apply (productSliceLeft_over f g s hs) U _).trans
    (CubeRelativeSectionsPullback.Construction.CubeCech.relativeSectionsPullback_apply _ _ _ _ _ x)

theorem productSliceLeftLinearMap_tensor (U : X.Opens) (V : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hsV : ⊤ ≤ s ⁻¹ᵁ V)
    (z : (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) ⊗[k]
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op V)) :
    productSliceLeftLinearMap f g s hs U V hsV
      (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g U V hU hV z) =
      TensorProduct.rid k _ (TensorProduct.map LinearMap.id (CubePointEvaluation.Construction.CubeCech.pointEvaluationLinearMap g s hs V hsV) z) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul x y =>
    exact (productSliceLeftLinearMap_apply f g s hs U V hsV _).trans
      (CubeProductSlices.Construction.CubeCech.productSliceLeftSectionMap_tmul f g s hs U V hU hV hsV x y)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSliceLinear.Construction.CubeCech
