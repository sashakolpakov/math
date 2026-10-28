import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechMixed

/-! # Cube Rectangle Cech -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech

noncomputable section

/-! The low-degree double Cech complex of a product cover, in actual sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

abbrev rectangleCech00 := ∀ i j,
  (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
    (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j)))

abbrev rectangleCech10 := ∀ i i' j,
  (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
    (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j)))

abbrev rectangleCech01 := ∀ i j j',
  (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
    (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j')))

abbrev rectangleCech11 := ∀ i i' j j',
  (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
    (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j ⊓ V j')))

def rectangleCech00Eval (i : ι) (j : κ) : rectangleCech00 f g U V →ₗ[k]
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j))) where
  toFun z := z i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rectangleCech10Eval (i i' : ι) (j : κ) : rectangleCech10 f g U V →ₗ[k]
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j))) where
  toFun z := z i i' j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rectangleCech01Eval (i : ι) (j j' : κ) : rectangleCech01 f g U V →ₗ[k]
    (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)).obj.obj
      (op (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j'))) where
  toFun z := z i j j'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rectangleCechD00h : rectangleCech00 f g U V →ₗ[k] rectangleCech10 f g U V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun i' ↦ LinearMap.pi fun j ↦
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i') (𝟙 (V j))).comp
      (rectangleCech00Eval f g U V i' j) -
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i) (𝟙 (V j))).comp
      (rectangleCech00Eval f g U V i j)

def rectangleCechD00v : rectangleCech00 f g U V →ₗ[k] rectangleCech01 f g U V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦ LinearMap.pi fun j' ↦
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i)) (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j')).comp
      (rectangleCech00Eval f g U V i j') -
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i)) (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j)).comp
      (rectangleCech00Eval f g U V i j)

def rectangleCechD10v : rectangleCech10 f g U V →ₗ[k] rectangleCech11 f g U V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun i' ↦ LinearMap.pi fun j ↦ LinearMap.pi fun j' ↦
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i ⊓ U i'))
      (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j')).comp
        (rectangleCech10Eval f g U V i i' j') -
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i ⊓ U i'))
      (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j)).comp
        (rectangleCech10Eval f g U V i i' j)

def rectangleCechD01h : rectangleCech01 f g U V →ₗ[k] rectangleCech11 f g U V :=
  LinearMap.pi fun i ↦ LinearMap.pi fun i' ↦ LinearMap.pi fun j ↦ LinearMap.pi fun j' ↦
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i')
      (𝟙 (V j ⊓ V j'))).comp
        (rectangleCech01Eval f g U V i' j j') -
    (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i)
      (𝟙 (V j ⊓ V j'))).comp
        (rectangleCech01Eval f g U V i j j')

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))
    (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

theorem rectangleCechD00h_comparison (z) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU
      (TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id z) =
    rectangleCechD00h f g U V (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z) := by
  funext i i' j
  exact CubeProductCechDifferentials.Construction.CubeCech.productCech_horizontal_differential f g U V hU hV hUU z i i' j

theorem rectangleCechD00v_comparison (z) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV
      (TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) z) =
    rectangleCechD00v f g U V (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z) := by
  funext i j j'
  exact CubeProductCechDifferentials.Construction.CubeCech.productCech_vertical_differential f g U V hU hV hVV z i j j'

theorem rectangleCechD10v_comparison (z) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV
      (TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) z) =
    rectangleCechD10v f g U V (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU z) := by
  funext i i' j j'
  exact CubeProductCechMixed.Construction.CubeCech.productCech_mixed_vertical_differential f g U V hV hUU hVV z i i' j j'

theorem rectangleCechD01h_comparison (z) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech11Equiv f g U V hUU hVV
      (TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id z) =
    rectangleCechD01h f g U V (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV z) := by
  funext i i' j j'
  exact CubeProductCechMixed.Construction.CubeCech.productCech_mixed_horizontal_differential f g U V hU hUU hVV z i i' j j'

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCech.Construction.CubeCech
