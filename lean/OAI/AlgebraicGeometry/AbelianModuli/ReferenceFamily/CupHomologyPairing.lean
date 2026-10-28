import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.Multiplication
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation

/-! # Cup Homology Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupHomologyPairing

noncomputable section

/-! Evaluation of the actual degree-two cup product on the original
abelian homology pairing is the alternating determinant of H1 periods. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback

theorem singularH1_cup_antisymm (X : TopCat.{0})
    (a b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1) :
    AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 a b = -AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X 1 1 b a := by
  simpa [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast] using AlgebraicTopology.Products.CupGradedCommutativity.singularCohomologyCup_graded_comm X a b

theorem homologyClassPairing_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a b : A.variety.rationalCohomology 1) (x y : HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) :
    HomologyCrossPairing.homologyClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b) x y =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a x *
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b y -
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b x *
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a y := by
  let : ∀ n, FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).homology n) :=
    fun n => by
      let : FiniteDimensional ℚ (A.variety.rationalCohomology n) :=
        AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety n
      exact AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.finite_homology_of_finite_cohomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) n
  rw [← CrossClassEvaluation.crossClassPairing_multiplication, AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) 1 1 a b,
    Product.Multiplication.abelianH1_multiplication, Product.Multiplication.abelianH1_multiplication]
  simp only [map_add, LinearMap.add_apply]
  have hl := congrArg (fun f => f x y)
    (CrossClassEvaluation.crossClassPairing_fst (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b))
  have hr := congrArg (fun f => f x y)
    (CrossClassEvaluation.crossClassPairing_snd (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b))
  rw [AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback TopCat.prodFst 1 1 a b] at hl
  rw [AlgebraicTopology.Kunneth.CupPullbackSingular.Construction.CupPullback.singularCohomologyCup_pullback TopCat.prodSnd 1 1 a b] at hr
  change CrossClassEvaluation.crossClassPairing _ _ (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup _ 1 1 (Product.Multiplication.productH1Left A a) (Product.Multiplication.productH1Left A b)) x y = 0 at hl
  change CrossClassEvaluation.crossClassPairing _ _ (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup _ 1 1 (Product.Multiplication.productH1Right A a) (Product.Multiplication.productH1Right A b)) x y = 0 at hr
  rw [hl, hr, zero_add, add_zero,
    singularH1_cup_antisymm (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) (Product.Multiplication.productH1Right A a) (Product.Multiplication.productH1Left A b),
    map_neg, LinearMap.neg_apply, LinearMap.neg_apply]
  dsimp only [Product.Multiplication.productH1Left, Product.Multiplication.productH1Right]
  rw [CrossClassEvaluation.crossClassPairing_externalCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) b a x y,
    CrossClassEvaluation.crossClassPairing_externalCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) a b x y]
  ring

theorem alternatingClassPairing_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a b : A.variety.rationalCohomology 1) (x y : HomologyCrossPairing.firstHomology (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) :
    HomologyCrossPairing.alternatingClassPairing (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 1 a b) x y =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a x *
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b y -
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 b x *
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 1 a y := by
  change (1 / 2 : ℚ) * (_ - _) = _
  simp only [LinearMap.flip_apply]
  rw [homologyClassPairing_cup, homologyClassPairing_cup]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CupHomologyPairing
