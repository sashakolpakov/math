import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRectangleCech
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeOpenCechCocycles

/-! # Cube Product Cech Cocycles -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech

noncomputable section

/-! Horizontal and vertical components determine a Cech cocycle on a product cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u v w

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ι : Type v} {κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens)

abbrev rectangleOpenCover (p : Σ _ : ι, κ) := CubeProductSections.Construction.CubeCech.productRectangle f g (U p.1) (V p.2)

abbrev rectangleOrdinaryCech1 := OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1
  (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)) (rectangleOpenCover f g U V)

def rectangleHorizontalComponent (z : rectangleOrdinaryCech1 f g U V) : CubeRectangleCech.Construction.CubeCech.rectangleCech10 f g U V :=
  fun i i' j ↦ CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 _ (rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j)))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j)))

def rectangleVerticalComponent (z : rectangleOrdinaryCech1 f g U V) : CubeRectangleCech.Construction.CubeCech.rectangleCech01 f g U V :=
  fun i j j' ↦ CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 _ (rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i, j'⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i) (V j ⊓ V j'))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_left))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i)) (homOfLE inf_le_right))

theorem rectangleHorizontalComponent_sub (z w : rectangleOrdinaryCech1 f g U V) :
    rectangleHorizontalComponent f g U V (z - w) =
      rectangleHorizontalComponent f g U V z - rectangleHorizontalComponent f g U V w := by
  funext i i' j
  exact CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_sub _ _ z w _ _ _ _ _

theorem rectangleVerticalComponent_sub (z w : rectangleOrdinaryCech1 f g U V) :
    rectangleVerticalComponent f g U V (z - w) =
      rectangleVerticalComponent f g U V z - rectangleVerticalComponent f g U V w := by
  funext i j j'
  exact CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_sub _ _ z w _ _ _ _ _

theorem rectangleHorizontalComponent_d0 (t : CubeRectangleCech.Construction.CubeCech.rectangleCech00 f g U V) :
    rectangleHorizontalComponent f g U V
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
        (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2)) = CubeRectangleCech.Construction.CubeCech.rectangleCechD00h f g U V t := by
  funext i i' j
  exact CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_d0 _ _ _ _ _ _ _ _

theorem rectangleVerticalComponent_d0 (t : CubeRectangleCech.Construction.CubeCech.rectangleCech00 f g U V) :
    rectangleVerticalComponent f g U V
      (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
        (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2)) = CubeRectangleCech.Construction.CubeCech.rectangleCechD00v f g U V t := by
  funext i j j'
  exact CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_d0 _ _ _ _ _ _ _ _

theorem rectangleCocycle_zero_of_components (z : rectangleOrdinaryCech1 f g U V)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (rectangleOpenCover f g U V) z)
    (ha : rectangleHorizontalComponent f g U V z = 0)
    (hb : rectangleVerticalComponent f g U V z = 0) : z = 0 := by
  funext p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  let F := CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)
  let W := rectangleOpenCover f g U V ⟨i, j⟩ ⊓ rectangleOpenCover f g U V ⟨i', j'⟩
  have hW₁ : W ≤ CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j) := by
    intro x hx
    exact ⟨⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  have hW₂ : W ≤ CubeProductSections.Construction.CubeCech.productRectangle f g (U i') (V j ⊓ V j') := by
    intro x hx
    exact ⟨hx.2.1, hx.1.2, hx.2.2⟩
  have hW₃ : W ≤ rectangleOpenCover f g U V ⟨i', j⟩ := by
    intro x hx
    exact ⟨hx.2.1, hx.1.2⟩
  have h₁ := CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_comp F (rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i ⊓ U i') (V j)) W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_left) (𝟙 (V j)))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (homOfLE inf_le_right) (𝟙 (V j))) hW₁
  have ha' := congrFun (congrFun (congrFun ha i) i') j
  have hz₁ : CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 F (rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j⟩ W
      inf_le_left hW₃ = 0 :=
    h₁.symm.trans ((congrArg (F.obj.map (homOfLE hW₁).op) ha').trans (map_zero _))
  have h₂ := CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_comp F (rectangleOpenCover f g U V) z ⟨i', j⟩ ⟨i', j'⟩
    (CubeProductSections.Construction.CubeCech.productRectangle f g (U i') (V j ⊓ V j')) W
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i')) (homOfLE inf_le_left))
    (CubeProductSectionsNaturality.Construction.CubeCech.productRectangle_mono f g (𝟙 (U i')) (homOfLE inf_le_right)) hW₂
  have hb' := congrFun (congrFun (congrFun hb i') j) j'
  have hz₂ : CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1 F (rectangleOpenCover f g U V) z ⟨i', j⟩ ⟨i', j'⟩ W
      hW₃ inf_le_right = 0 :=
    h₂.symm.trans ((congrArg (F.obj.map (homOfLE hW₂).op) hb').trans (map_zero _))
  have h := hz ⟨i, j⟩ ⟨i', j⟩ ⟨i', j'⟩ W inf_le_left hW₃ inf_le_right
  rw [hz₁, hz₂, zero_add] at h
  exact (CubeOpenCechCocycles.Construction.CubeCech.openCechRestrict1_self F (rectangleOpenCover f g U V) z ⟨i, j⟩ ⟨i', j'⟩).symm.trans h.symm

theorem rectangleCocycle_isBoundary_of_components (z : rectangleOrdinaryCech1 f g U V)
    (hz : CubeOpenCechCocycles.Construction.CubeCech.IsOpenCechCocycle (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (rectangleOpenCover f g U V) z) (t : CubeRectangleCech.Construction.CubeCech.rectangleCech00 f g U V)
    (ha : CubeRectangleCech.Construction.CubeCech.rectangleCechD00h f g U V t = rectangleHorizontalComponent f g U V z)
    (hb : CubeRectangleCech.Construction.CubeCech.rectangleCechD00v f g U V t = rectangleVerticalComponent f g U V z) :
    OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f))
      (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2) = z := by
  let F := CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf (pullback.fst f g ≫ f)
  let d := OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2)
  have hzero : z - d = 0 := by
    apply rectangleCocycle_zero_of_components f g U V (z - d)
      (CubeOpenCechCocycles.Construction.CubeCech.openCechCocycle_sub F _ z d hz (CubeOpenCechCocycles.Construction.CubeCech.openCechD0_isCocycle F _ _))
    · rw [rectangleHorizontalComponent_sub]
      change rectangleHorizontalComponent f g U V z - rectangleHorizontalComponent f g U V
        (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2)) = 0
      rw [rectangleHorizontalComponent_d0, ha, sub_self]
    · rw [rectangleVerticalComponent_sub]
      change rectangleVerticalComponent f g U V z - rectangleVerticalComponent f g U V
        (OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F (rectangleOpenCover f g U V) (fun p ↦ t p.1 p.2)) = 0
      rw [rectangleVerticalComponent_d0, hb, sub_self]
  exact (sub_eq_zero.mp hzero).symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeProductCechCocycles.Construction.CubeCech
