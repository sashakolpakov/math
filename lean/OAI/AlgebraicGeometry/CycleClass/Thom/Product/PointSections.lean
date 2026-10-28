import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract

/-! # Point Sections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointSections.Constructions

noncomputable section

/-! Actual product sections through a complex point. The section and
projection identities give smoothness descent to each factor point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothRetract.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def structurePointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : X ⟶ Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) :=
  Over.homMk X.hom (Category.comp_id _)

theorem point_structurePointMap (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    p ≫ structurePointMap X = 𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) := by
  apply Over.OverMorphism.ext
  exact p.w

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))

def productSectionLeft (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) : X ⟶ Z :=
  BinaryFan.IsLimit.lift hprod (𝟙 X) (structurePointMap X ≫ q)

def productSectionRight (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : Y ⟶ Z :=
  BinaryFan.IsLimit.lift hprod (structurePointMap Y ≫ p) (𝟙 Y)

@[reassoc (attr := simp)]
theorem productSectionLeft_fst (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    productSectionLeft X Y Z πX πY hprod q ≫ πX = 𝟙 X := BinaryFan.IsLimit.lift_fst hprod _ _

@[reassoc (attr := simp)]
theorem productSectionLeft_snd (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    productSectionLeft X Y Z πX πY hprod q ≫ πY = structurePointMap X ≫ q :=
  BinaryFan.IsLimit.lift_snd hprod _ _

@[reassoc (attr := simp)]
theorem productSectionRight_fst (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    productSectionRight X Y Z πX πY hprod p ≫ πX = structurePointMap Y ≫ p :=
  BinaryFan.IsLimit.lift_fst hprod _ _

@[reassoc (attr := simp)]
theorem productSectionRight_snd (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    productSectionRight X Y Z πX πY hprod p ≫ πY = 𝟙 Y := BinaryFan.IsLimit.lift_snd hprod _ _

theorem productSectionLeft_point (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) :
    (z ≫ πX) ≫ productSectionLeft X Y Z πX πY hprod (z ≫ πY) = z := by
  apply BinaryFan.IsLimit.hom_ext hprod
  · change ((z ≫ πX) ≫ productSectionLeft X Y Z πX πY hprod (z ≫ πY)) ≫ πX = z ≫ πX
    rw [Category.assoc, productSectionLeft_fst, Category.comp_id]
  · change ((z ≫ πX) ≫ productSectionLeft X Y Z πX πY hprod (z ≫ πY)) ≫ πY = z ≫ πY
    rw [Category.assoc, productSectionLeft_snd, ← Category.assoc, point_structurePointMap, Category.id_comp]

theorem productSectionRight_point (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) :
    (z ≫ πY) ≫ productSectionRight X Y Z πX πY hprod (z ≫ πX) = z := by
  apply BinaryFan.IsLimit.hom_ext hprod
  · change ((z ≫ πY) ≫ productSectionRight X Y Z πX πY hprod (z ≫ πX)) ≫ πX = z ≫ πX
    rw [Category.assoc, productSectionRight_fst, ← Category.assoc, point_structurePointMap, Category.id_comp]
  · change ((z ≫ πY) ≫ productSectionRight X Y Z πX πY hprod (z ≫ πX)) ≫ πY = z ≫ πY
    rw [Category.assoc, productSectionRight_snd, Category.comp_id]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointSections.Constructions
