import OAI.AlgebraicGeometry.CycleClass.Thom.ReducedProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension

/-! # Graded Product Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GradedProductSupport.Constructions

noncomputable section

/-! The external product of two genuine integral supports is exactly the
unit cycle on their reduced product, in the sum of their actual codimensions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ReducedProduct.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

theorem supportInDegree_eq_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W = p) :
    IntersectionGeometry.supportInDegree X p W = Finsupp.single ⟨W, hW⟩ 1 := by
  classical
  unfold IntersectionGeometry.supportInDegree
  rw [dite_eq_left hW]

variable (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
  (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport q)

def productDimensionSupport : Z.DimensionCycleSupport (p + q) :=
  ⟨Product.SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A.val B.val Z.toOver πX πY hprod,
    (Product.SupportCodimension.Constructions.productIrreducibleSupport_codimension X Y Z πX πY hprod A.val B.val).trans
      (congrArg₂ (· + ·) A.property B.property)⟩

theorem reducedProductCycle_eq_single :
    IntersectionGeometry.reducedClosedCycle Z (p + q) (IntersectionGeometry.productClosedSupport X Y Z πX πY A.val B.val) =
      Finsupp.single (productDimensionSupport X Y Z πX πY hprod p q A B) 1 := by
  classical
  rw [ReducedProduct.Constructions.reducedProductCycle_eq_supportInDegree X Y Z πX πY hprod]
  exact supportInDegree_eq_single Z (p + q) _
    (productDimensionSupport X Y Z πX πY hprod p q A B).property

theorem exteriorCycleProduct_unit_supports :
    IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q (Finsupp.single A 1) (Finsupp.single B 1) =
      Finsupp.single (productDimensionSupport X Y Z πX πY hprod p q A B) 1 := by
  rw [IntersectionGeometry.exteriorCycleProduct_single, one_mul, one_smul, reducedProductCycle_eq_single]

theorem exteriorCycleProduct_weighted_supports (r s : ℚ) :
    IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q (Finsupp.single A r) (Finsupp.single B s) =
      Finsupp.single (productDimensionSupport X Y Z πX πY hprod p q A B) (r * s) := by
  rw [IntersectionGeometry.exteriorCycleProduct_single, reducedProductCycle_eq_single, Finsupp.smul_single, smul_eq_mul, mul_one]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GradedProductSupport.Constructions
