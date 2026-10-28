import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCup
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Rational Cup Unit -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCupUnit.CM.Construction

noncomputable section

/-! Rational coefficient inclusion preserves the actual cup unit
and commutes with equality transport of cohomological degrees. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

theorem rationalToComplexCochain_unit (X : TopCat.{0}) :
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f 0 (AlgebraicTopology.Products.Cup.cupUnit (R := ℚ) (TopCat.toSSet.obj X)) =
      AlgebraicTopology.Products.Cup.cupUnit (R := ℂ) (TopCat.toSSet.obj X) := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ)
  intro s
  have h := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X 0 (AlgebraicTopology.Products.Cup.cupUnit (R := ℚ) (TopCat.toSSet.obj X)) s
  have hQ := AlgebraicTopology.Products.Cup.evaluation_cupUnit (R := ℚ) (TopCat.toSSet.obj X) s
  have hC := AlgebraicTopology.Products.Cup.evaluation_cupUnit (R := ℂ) (TopCat.toSSet.obj X) s
  exact h.trans ((congrArg (fun t : ℚ => (t : ℂ)) hQ).trans ((Rat.cast_one (α := ℂ)).trans hC.symm))

theorem rationalToComplexCohomology_unit (X : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit (R := ℚ) (TopCat.toSSet.obj X)) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit (R := ℂ) (TopCat.toSSet.obj X) := by
  have h := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class X 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (R := ℚ) (TopCat.toSSet.obj X))
  refine h.trans ?_
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) 0)
  apply Subtype.ext
  exact rationalToComplexCochain_unit X

theorem rationalToComplexCohomology_cast (X : TopCat.{0}) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X m
      (cast (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X k : Type)) h) a) =
    cast (congrArg (fun k => (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X k : Type)) h)
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n a) := by
  subst m
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCupUnit.CM.Construction
