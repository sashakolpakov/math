import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechDescent
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement

/-! # Descent Refinement -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular

noncomputable section

/-! Refinement and integer multiplication preserve the actual singular Cech descent equations. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Refinement.RationalCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I J : Type} {U : I → Opens X}
  {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : CechDescent.SingularCechDescentData c U)

def CechDescent.SingularCechDescentData.refine (V : J → Opens X) (r : J → I) (hr : ∀ j, V j ≤ U (r j)) :
    CechDescent.SingularCechDescentData c V where
  vertical := Rational.Cech.RationalCech.cechRefinementMap ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 1)
    U V r hr 0 d.vertical
  vertical_d := by
    rw [Cech.Refinement.RationalCech.cechCoefficientMap_refinement, d.vertical_d]
    exact ConcreteCategory.congr_hom
      (Refinement.RationalCech.globalSingularCechColumnAugmentation_refinement X U V r hr (ModuleCat.of ℚ ℚ) 2) c.val
  horizontal := Rational.Cech.RationalCech.cechRefinementMap ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0)
    U V r hr 1 d.horizontal
  horizontal_d := by
    rw [Cech.Refinement.RationalCech.cechCoefficientMap_refinement, d.horizontal_d, Rational.Cech.RationalCech.cechRefinementMap_delta]

def CechDescent.SingularCechDescentData.nsmul (N : ℕ) : CechDescent.SingularCechDescentData (N • c) U where
  vertical := N • d.vertical
  vertical_d := by
    rw [map_nsmul, d.vertical_d]
    exact (map_nsmul ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2).hom N c.val).symm
  horizontal := N • d.horizontal
  horizontal_d := by
    rw [map_nsmul, d.horizontal_d, map_nsmul]

theorem CechDescent.SingularCechDescentData.refine_cocycle
    (V : J → Opens X) (r : J → I) (hr : ∀ j, V j ≤ U (r j))
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    Cech.Obj.RationalCech.locallyConstantCechEvaluation X V 2
        (Rational.Cech.RationalCech.cechRefinementMap (Cech.Obj.RationalCech.locallyConstantPresheaf X) U V r hr 2 k) =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) V 1
        (d.refine V r hr).horizontal := by
  rw [Cech.Refinement.RationalCech.cechCoefficientMap_refinement, hk, map_neg]
  erw [Rational.Cech.RationalCech.cechRefinementMap_delta]
  rfl

theorem CechDescent.SingularCechDescentData.nsmul_cocycle (N : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U 2)
    (hk : Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 k =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 d.horizontal) :
    Cech.Obj.RationalCech.locallyConstantCechEvaluation X U 2 (N • k) =
      -Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X 0) U 1 (d.nsmul N).horizontal := by
  rw [map_nsmul, hk]
  change N • (-Rational.Cech.RationalCech.cechDelta _ U 1 d.horizontal) = -Rational.Cech.RationalCech.cechDelta _ U 1 (N • d.horizontal)
  rw [map_nsmul, smul_neg]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular
