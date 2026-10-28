import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexCochains
import OAI.AlgebraicGeometry.DivisorClass.Chern.RestrictionCochainEvaluation

/-! # Complex Evaluation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexEvaluation

noncomputable section

/-! The original coefficient cochain map casts the actual value on each simplex. -/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalToComplexCochainMap_evaluation (X : TopCat.{0}) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (ComplexCochains.rationalToComplexCochainMap X).f n ≫
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
        (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s) =
      AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s ≫ ComplexCochains.rationalRestrictedComplexInclusion := by
  rw [ComplexCochains.rationalToComplexCochainMap, HomologicalComplex.comp_f, Category.assoc,
    RestrictionCochainEvaluation.singularCochainsRestrictScalarsIso_inv_evaluation]
  exact AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientCochainMap_evaluation ComplexCochains.rationalRestrictedComplexInclusion X s

theorem rationalToComplexCochainMap_apply (X : TopCat.{0}) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) s ((ComplexCochains.rationalToComplexCochainMap X).f n c) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) s c : ℂ) :=
  ConcreteCategory.congr_hom (rationalToComplexCochainMap_evaluation X s) c

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ComplexEvaluation
