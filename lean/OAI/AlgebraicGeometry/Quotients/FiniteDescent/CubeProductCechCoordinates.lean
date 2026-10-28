import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSections
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Cube Product Cech Coordinates -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCoordinates.Construction.CubeCech

noncomputable section

/-! Tensor coordinates for finite families of affine rectangles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))

def productCech00Equiv :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V ≃ₗ[k]
    ∀ i j, (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j))) :=
  (TensorProduct.piLeft k (OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V)
    (fun i ↦ (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op (U i)))).trans
      (LinearEquiv.piCongrRight fun i ↦
        (TensorProduct.piRight k k ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op (U i)))
          (fun j ↦ (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op (V j)))).trans
            (LinearEquiv.piCongrRight fun j ↦ CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g
              (U i) (V j) (hU i) (hV j)))

theorem productCech00Equiv_tmul
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i : ι) (j : κ) :
    productCech00Equiv f g U V hU hV (x ⊗ₜ[k] y) i j =
      CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g (U i) (V j) (x i) *
        CubeProductSections.Construction.CubeCech.productRectangleRightMap f g (U i) (V j) (y j) := by
  simp [productCech00Equiv, TensorProduct.piLeft, TensorProduct.piRight,
    CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul]
  rfl

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCoordinates.Construction.CubeCech
