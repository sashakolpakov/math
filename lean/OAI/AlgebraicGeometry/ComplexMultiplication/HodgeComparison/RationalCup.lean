import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Rational Cup -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction

noncomputable section

/-! The literal rational-to-complex coefficient inclusion preserves
the actual front/back cup product on cochains and cohomology. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CupCohomology
open scoped Simplicial

theorem rationalToComplexCochain_cup (X : TopCat.{0}) (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X q) :
    (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f (p + q)
      (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ) a b) =
    AlgebraicTopology.Products.Cup.cupWith (M := ModuleCat.of ℂ ℂ) (N := ModuleCat.of ℂ ℂ) (L := ModuleCat.of ℂ ℂ)
      (TopCat.toSSet.obj X) (LinearMap.mul ℂ ℂ)
      ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f p a) ((PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f q b) := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ)
  intro s
  let aC : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).X p := (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f p a
  let bC : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X).X q := (PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f q b
  have hleft := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X (p + q)
    (AlgebraicTopology.Products.Cup.cupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ) a b) s
  have hQ := AlgebraicTopology.Products.Cup.evaluation_cupWith (L := ModuleCat.of ℚ ℚ)
    (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ) a b s
  have hC := AlgebraicTopology.Products.Cup.evaluation_cupWith (L := ModuleCat.of ℂ ℂ)
    (TopCat.toSSet.obj X) (LinearMap.mul ℂ ℂ) aC bC s
  have ha := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X p a (AlgebraicTopology.Products.SimplexFaceIdentities.frontFace (TopCat.toSSet.obj X) p q s)
  have hb := PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X q b (AlgebraicTopology.Products.SimplexFaceIdentities.backFace (TopCat.toSSet.obj X) p q s)
  refine hleft.trans ((congrArg (fun t : ℚ => (t : ℂ)) hQ).trans ?_)
  refine (Rat.cast_mul _ _).trans ?_
  exact (congrArg₂ (fun x y : ℂ => x * y) ha.symm hb.symm).trans hC.symm

theorem complexCocycleOfRational_cup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X q) :
    PositiveCohomologyConjugation.CM.Construction.complexCocycleOfRational X (p + q)
      (AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℚ ℚ) p q a b) =
    AlgebraicTopology.Products.CupCohomology.cocycleCupWith (TopCat.toSSet.obj X) (LinearMap.mul ℂ ℂ) p q
      (PositiveCohomologyConjugation.CM.Construction.complexCocycleOfRational X p a) (PositiveCohomologyConjugation.CM.Construction.complexCocycleOfRational X q b) := by
  apply Subtype.ext
  exact rationalToComplexCochain_cup X p q a.val b.val

theorem rationalToComplexCohomology_cup (X : TopCat.{0}) (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X (p + q) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X p q (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X p a)
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X q b) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X p a
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X q b
  rw [AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class, PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class,
    PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class, PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class,
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup_class_class, complexCocycleOfRational_cup]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction
