import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechOverlaps
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductSectionsOneFactor

/-! # Cube Product Cech Differentials -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechDifferentials.Construction.CubeCech

noncomputable section

/-! The degree-zero Cech differentials agree with the tensor differentials in product coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hUU : ∀ i i', IsAffineOpen (U i ⊓ U i'))

theorem productCech_horizontal_differential
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i i' : ι) (j : κ) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv f g U V hV hUU
      (TensorProduct.map (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U) LinearMap.id z) i i' j =
    ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i') (𝟙 (V j))
      (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z i' j) -
    ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i) (𝟙 (V j))
      (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z i j) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply, hz, hw]
    abel
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    have hleft := (CubeProductCechOverlaps.Construction.CubeCech.productCech10Equiv_tmul f g U V hV hUU
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U x) y i i' j).trans
        (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i ⊓ U i') (V j)
          (hUU i i') (hV j) _ (y j)).symm
    refine hleft.trans ?_
    change CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g (U i ⊓ U i') (V j) (hUU i i') (hV j)
      (((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map
        (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i').op (x i') -
        (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.map
          (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i).op (x i)) ⊗ₜ[k] y j) = _
    rw [TensorProduct.sub_tmul, map_sub]
    apply congrArg₂ (fun a b ↦ a - b)
    · exact (ProductSectionsOneFactor.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict_left_tmul f g
        (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i') (V j) (hU i') (hUU i i') (hV j)
        (x i') (y j)).trans
          (congrArg (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g
            (homOfLE inf_le_right : U i ⊓ U i' ⟶ U i') (𝟙 (V j)))
            ((CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i') (V j) (hU i') (hV j)
              (x i') (y j)).trans (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g U V hU hV x y i' j).symm))
    · exact (ProductSectionsOneFactor.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict_left_tmul f g
        (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i) (V j) (hU i) (hUU i i') (hV j)
        (x i) (y j)).trans
          (congrArg (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g
            (homOfLE inf_le_left : U i ⊓ U i' ⟶ U i) (𝟙 (V j)))
            ((CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i) (V j) (hU i) (hV j)
              (x i) (y j)).trans (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g U V hU hV x y i j).symm))

variable (hVV : ∀ j j', IsAffineOpen (V j ⊓ V j'))

theorem productCech_vertical_differential
    (z : OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f) U ⊗[k]
      OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) (i : ι) (j j' : κ) :
    CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv f g U V hU hVV
      (TensorProduct.map LinearMap.id (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V) z) i j j' =
    ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i)) (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j')
      (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z i j') -
    ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i)) (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j)
      (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv f g U V hU hV z i j) := by
  induction z using TensorProduct.inductionOn with
  | add z w hz hw =>
    simp only [map_add, Pi.add_apply, hz, hw]
    abel
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    have hleft := (CubeProductCechOverlaps.Construction.CubeCech.productCech01Equiv_tmul f g U V hU hVV
      x (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g) V y) i j j').trans
        (CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i) (V j ⊓ V j')
          (hU i) (hVV j j') (x i) _).symm
    refine hleft.trans ?_
    change CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv f g (U i) (V j ⊓ V j') (hU i) (hVV j j')
      (x i ⊗ₜ[k] ((CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.map
        (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j').op (y j') -
        (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf g).obj.map
          (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j).op (y j))) = _
    rw [TensorProduct.tmul_sub, map_sub]
    apply congrArg₂ (fun a b ↦ a - b)
    · exact (ProductSectionsOneFactor.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict_right_tmul f g
        (U i) (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j') (hU i) (hV j') (hVV j j')
        (x i) (y j')).trans
          (congrArg (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i))
            (homOfLE inf_le_right : V j ⊓ V j' ⟶ V j'))
            ((CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i) (V j') (hU i) (hV j')
              (x i) (y j')).trans (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g U V hU hV x y i j').symm))
    · exact (ProductSectionsOneFactor.Construction.CubeCech.productRectangleModuleSectionsEquiv_restrict_right_tmul f g
        (U i) (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j) (hU i) (hV j) (hVV j j')
        (x i) (y j)).trans
          (congrArg (ProductSectionsOneFactor.Construction.CubeCech.rectangleSectionRestriction f g (𝟙 (U i))
            (homOfLE inf_le_left : V j ⊓ V j' ⟶ V j))
            ((CubeProductSections.Construction.CubeCech.productRectangleModuleSectionsEquiv_tmul f g (U i) (V j) (hU i) (hV j)
              (x i) (y j)).trans (CubeProductCechCoordinates.Construction.CubeCech.productCech00Equiv_tmul f g U V hU hV x y i j).symm))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechDifferentials.Construction.CubeCech
