import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCoordinates
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductSectionsNaturality

/-! # Cube Product Cech Overlaps -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech

noncomputable section

/-! Tensor coordinates for horizontal, vertical, and mixed overlaps of a finite product cover. -/

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

def productCech10Equiv :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V ≃ₗ[k]
    ∀ i i' j, (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j))) :=
  (TensorProduct.congr
    (LinearEquiv.piCurry k (fun i i' ↦
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op (U i ⊓ U i')))).symm
    (LinearEquiv.refl k _)).trans
      ((CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g (fun p : Σ _ : ι, ι ↦ U p.1 ⊓ U p.2) V
        (fun p ↦ hUU p.1 p.2) hV).trans
          (LinearEquiv.piCurry k (fun i i' ↦ ∀ j,
            (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
              (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j))))))

def productCech01Equiv :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V ≃ₗ[k]
    ∀ i j j', (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j'))) :=
  (TensorProduct.congr (LinearEquiv.refl k _)
    (LinearEquiv.piCurry k (fun j j' ↦
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op (V j ⊓ V j')))).symm).trans
      ((CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U (fun p : Σ _ : κ, κ ↦ V p.1 ⊓ V p.2)
        hU (fun p ↦ hVV p.1 p.2)).trans
          (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCurry k (fun j j' ↦
            (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
              (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j'))))))

def productCech11Equiv :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V ≃ₗ[k]
    ∀ i i' j j', (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j'))) :=
  (TensorProduct.congr
    (LinearEquiv.piCurry k (fun i i' ↦
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op (U i ⊓ U i')))).symm
    (LinearEquiv.piCurry k (fun j j' ↦
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.obj (op (V j ⊓ V j')))).symm).trans
      ((CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g (fun p : Σ _ : ι, ι ↦ U p.1 ⊓ U p.2)
        (fun p : Σ _ : κ, κ ↦ V p.1 ⊓ V p.2)
        (fun p ↦ hUU p.1 p.2) (fun p ↦ hVV p.1 p.2)).trans
          ((LinearEquiv.piCurry k (fun i i' ↦ ∀ p : Σ _ : κ, κ,
            (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
              (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V p.1 ⊓ V p.2))))).trans
                (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun i' ↦
                  LinearEquiv.piCurry k (fun j j' ↦
                    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
                      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j')))))))

theorem productCech10Equiv_tmul
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i i' : ι) (j : κ) :
    productCech10Equiv f g U V hV hUU (x ⊗ₜ[k] y) i i' j =
      CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g (U i ⊓ U i') (V j) (x i i') *
        CubeProductSections.Construction.CubeCech.productRectangleRightMap f g (U i ⊓ U i') (V j) (y j) := by
  simp [productCech10Equiv, LinearEquiv.piCurry]
  exact CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g (fun p : Σ _ : ι, ι ↦ U p.1 ⊓ U p.2) V
    (fun p ↦ hUU p.1 p.2) hV (Sigma.uncurry x) y ⟨i, i'⟩ j

theorem productCech01Equiv_tmul
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i : ι) (j j' : κ) :
    productCech01Equiv f g U V hU hVV (x ⊗ₜ[k] y) i j j' =
      CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g (U i) (V j ⊓ V j') (x i) *
        CubeProductSections.Construction.CubeCech.productRectangleRightMap f g (U i) (V j ⊓ V j') (y j j') := by
  simp [productCech01Equiv, LinearEquiv.piCurry]
  exact CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g U (fun p : Σ _ : κ, κ ↦ V p.1 ⊓ V p.2)
    hU (fun p ↦ hVV p.1 p.2) x (Sigma.uncurry y) i ⟨j, j'⟩

theorem productCech11Equiv_tmul
    (x : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U)
    (y : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i i' : ι) (j j' : κ) :
    productCech11Equiv f g U V hUU hVV (x ⊗ₜ[k] y) i i' j j' =
      CubeProductSections.Construction.CubeCech.productRectangleLeftMap f g (U i ⊓ U i') (V j ⊓ V j') (x i i') *
        CubeProductSections.Construction.CubeCech.productRectangleRightMap f g (U i ⊓ U i') (V j ⊓ V j') (y j j') := by
  simp [productCech11Equiv, LinearEquiv.piCurry]
  exact CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g (fun p : Σ _ : ι, ι ↦ U p.1 ⊓ U p.2)
    (fun p : Σ _ : κ, κ ↦ V p.1 ⊓ V p.2)
    (fun p ↦ hUU p.1 p.2) (fun p ↦ hVV p.1 p.2)
    (Sigma.uncurry x) (Sigma.uncurry y) ⟨i, i'⟩ ⟨j, j'⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechOverlaps.Construction.CubeCech
