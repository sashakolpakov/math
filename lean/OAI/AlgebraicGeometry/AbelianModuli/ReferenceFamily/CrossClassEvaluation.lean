import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Cross Class Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation

noncomputable section

section

/-! Evaluation of degree-two classes on the actual (1,1) homology
product is bilinear, natural in both factors, and kills classes pulled
back from either single factor. -/

open _root_.CategoryTheory _root_.HomologicalComplex OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped TensorProduct

def crossClassPairing (X Y : TopCat.{0}) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) 2 →ₗ[ℚ]
      (HomologyCrossPairing.firstHomology X →ₗ[ℚ] HomologyCrossPairing.firstHomology Y →ₗ[ℚ] ℚ) where
  toFun c := TensorProduct.curry ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 c).comp
    (HomologyCrossNaturality.productHomologyCross11 X Y))
  map_add' c d := by
    ext x y
    change AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 (c + d) _ =
      AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 c _ +
        AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 d _
    rw [map_add, LinearMap.add_apply]
  map_smul' r c := by
    ext x y
    change AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 (r • c) _ =
      r • AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2 c _
    rw [map_smul, LinearMap.smul_apply]

theorem crossClassPairing_apply (X Y : TopCat.{0})
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) 2)
    (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    crossClassPairing X Y c x y = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X × Y)) 2 c
      (HomologyCrossNaturality.productHomologyCross11 X Y (x ⊗ₜ[ℚ] y)) := rfl

theorem crossClassPairing_naturality {X X' Y Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (X' × Y')) 2)
    (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    crossClassPairing X Y (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) 2 c) x y =
    crossClassPairing X' Y' c
      (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map f) 1 x) (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map g) 1 y) := by
  exact (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (X', Y'))) 2 c _).trans
      (congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (X' × Y')) 2 c)
        (HomologyCrossNaturality.productHomologyCross11_naturality f g x y))

theorem crossClassPairing_fst (X Y : TopCat.{0})
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    crossClassPairing X Y (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 2 c) = 0 := by
  ext x y
  have h := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (TopCat.prodFst (X := X) (Y := Y)) 2 c (HomologyCrossNaturality.productHomologyCross11 X Y (x ⊗ₜ[ℚ] y))
  exact h.trans
    ((congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 2 c)
      (HomologyCrossNaturality.productHomologyCross11_fst X Y x y)).trans (map_zero _))

theorem crossClassPairing_snd (X Y : TopCat.{0})
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 2) :
    crossClassPairing X Y (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 2 c) = 0 := by
  ext x y
  have h := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ)
    (TopCat.prodSnd (X := X) (Y := Y)) 2 c (HomologyCrossNaturality.productHomologyCross11 X Y (x ⊗ₜ[ℚ] y))
  exact h.trans
    ((congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y 2 c)
      (HomologyCrossNaturality.productHomologyCross11_snd X Y x y)).trans (map_zero _))

theorem crossClassPairing_multiplication (X : TopCat.{0}) (m : TopCat.of (X × X) ⟶ X)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    crossClassPairing X X (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) m 2 c) =
      HomologyCrossPairing.homologyClassPairing X m c := by
  ext x y
  exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) m 2 c _

theorem crossClassPairing_multiplication_difference (X : TopCat.{0})
    (m : TopCat.of (X × X) ⟶ X) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    crossClassPairing X X
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) m 2 c -
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst 2 c -
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd 2 c) =
      HomologyCrossPairing.homologyClassPairing X m c := by
  rw [map_sub, map_sub, crossClassPairing_fst, crossClassPairing_snd, sub_zero,
    sub_zero, crossClassPairing_multiplication]

end

/-! The original normalized singular cross product pairs with an
exterior cup product by the product of its two actual H1 evaluations. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open OAI.AlgebraicTopology.Kunneth.Add.Construction OAI.AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth
open OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof.Construction.CohomologyTensorNormalization
open scoped TensorProduct DirectSum

theorem crossClassPairing_externalCup (X Y : TopCat.{0})
    [∀ n, FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n)]
    [∀ n, FiniteDimensional ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).homology n)]
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 1)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 1)
    (x : HomologyCrossPairing.firstHomology X) (y : HomologyCrossPairing.firstHomology Y) :
    crossClassPairing X Y
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (TopCat.of (X × Y)) 1 1
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.prodFst (X := X) (Y := Y)) 1 a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (TopCat.prodSnd (X := X) (Y := Y)) 1 b)) x y =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 a x * AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y 1 b y := by
  let ij : AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs 2 := ⟨(1, 1), rfl⟩
  let c := DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs 2)
    (fun d => AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X d.val.1 ⊗[ℚ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y d.val.2) ij (a ⊗ₜ[ℚ] b)
  let z := DirectSum.lof ℚ (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs 2)
    (fun d => (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology d.val.1 ⊗[ℚ]
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).homology d.val.2) ij (x ⊗ₜ[ℚ] y)
  let H := ((AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.productHomotopyEquiv (k := ℚ) X Y).toHomologyIso 2).toLinearEquiv
  let K := AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X)
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y) 2
  have hc := AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv_lof_add X Y 1 1 a b
  have he : crossClassPairing X Y (AlgebraicTopology.Kunneth.CanonicalCohomology.Construction.CanonicalCohomologyKunneth.canonicalCohomologyEquiv X Y 2 c) x y =
      AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y 2 c z := by
    change AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2
      ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) 2).symm _)
        (H.symm (K z)) = _
    rw [LinearEquiv.apply_symm_apply]
    change AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y 2 c (K.symm (H (H.symm (K z)))) = _
    rw [H.apply_symm_apply, K.symm_apply_apply]
  have hv : AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y 2 c z =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X 1 a x * AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y 1 b y := by
    rw [AlgebraicTopology.Kunneth.CohomologyTensorLof.Construction.CohomologyTensorNormalization.cohomologySumDualEquiv_lof X Y 2 ij a b, AlgebraicTopology.Kunneth.CohomologyTensorLof.Construction.CohomologyTensorNormalization.directSumDualEquiv_lof_self]
    rfl
  exact (congrArg (fun c => crossClassPairing X Y c x y) hc).symm.trans (he.trans hv)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation
