import OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney
import OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof

/-! # Canonical Cohomology -/

namespace OAI.AlgebraicTopology.Kunneth.CanonicalCohomology

noncomputable section

section

/-! Exterior cup products and canonical tensor homology, on actual classes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct

namespace Construction.CupHomologyComparison

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof.Construction.CohomologyTensorNormalization

variable (k : Type) [Field k]

theorem cup_tensor_homology (X : ProductModelsAs.Construction.ProductModels.SpacePair) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) X.1 p)
    (d : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) X.2 q)
    (z : ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)).homology (p + q)) :
    CohomologyTensorLof.Construction.CohomologyTensorNormalization.cocycleTensorFunctional X.1 X.2 p q c d
      (HomologicalComplex.homologyMap (TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k X) (p + q) z) =
    Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (ProductModelsAs.Construction.ProductModels.productSpace.obj X) (p + q)
      (Products.CupCohomology.singularCohomologyCup (ProductModelsAs.Construction.ProductModels.productSpace.obj X) p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k)
          (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1) p (Cohomology.Singular.Representatives.singularClass (ModuleCat.of k k) X.1 p c))
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k)
          (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2) q (Cohomology.Singular.Representatives.singularClass (ModuleCat.of k k) X.2 q d))) z := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective ((ProductModelsAs.Construction.ProductModels.scalarChains k).obj (ProductModelsAs.Construction.ProductModels.productSpace.obj X)) (p + q) z
  erw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality (TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k X) (p + q) z]
  change TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X.1)
    (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X.2) p q _ _ _ _
    (Cohomology.Singular.ChainRepresentatives.chainClass _ (p + q) (Cohomology.Singular.EvaluationNaturality.chainCycleMap (TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k X) (p + q) z)) = _
  erw [TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_class]
  rw [Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv_apply (ProductModelsAs.Construction.ProductModels.productSpace.obj X) (p + q)]
  erw [Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class (ModuleCat.of k k)
      (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1) p c,
    Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class (ModuleCat.of k k)
      (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2) q d]
  erw [Products.CupCohomology.singularCohomologyCup_class_class (ProductModelsAs.Construction.ProductModels.productSpace.obj X)
    (Cohomology.Singular.RepresentativesNaturality.singularCocyclePullback (ModuleCat.of k k) (TopCat.prodFst : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.1) p c)
    (Cohomology.Singular.RepresentativesNaturality.singularCocyclePullback (ModuleCat.of k k) (TopCat.prodSnd : ProductModelsAs.Construction.ProductModels.productSpace.obj X ⟶ X.2) q d)]
  erw [Cohomology.Singular.Evaluation.singularEvaluation_class_class (ModuleCat.of k k) (ProductModelsAs.Construction.ProductModels.productSpace.obj X) (p + q)]
  exact TensorAlexanderWhitney.Construction.CupTensorComparison.cup_tensor_chain k X p q c.val d.val z.val

end Construction.CupHomologyComparison

end

/-! The cohomology Künneth isomorphism with its exterior-product normalization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.HomologicalComplex
open scoped TensorProduct DirectSum

namespace Construction.CanonicalCohomologyKunneth

open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.ProductAlexanderWhitney OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof.Construction.CohomologyTensorNormalization

variable {k : Type} [Field k]

def productHomotopyEquiv (X Y : TopCat.{0}) :
    HomotopyEquiv (Cohomology.Singular.Evaluation.singularScalarChains (R := k) (TopCat.of (X × Y)))
      (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X ⊗ Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) :=
  ((evaluation ProductModelsAs.Construction.ProductModels.SpacePair (ModuleCat.{0} k)).obj (X, Y)).mapHomotopyEquiv
    (TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.canonicalHomotopyEquiv k)

@[simp]
theorem productHomotopyEquiv_hom (X Y : TopCat.{0}) :
    (productHomotopyEquiv (k := k) X Y).hom = TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X, Y) := rfl

variable (X Y : TopCat.{0})
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n)]
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology n)]

def canonicalCohomologyEquiv (n : ℕ) :
    CohomologyTensorNe.Construction.CohomologyDecomposition.CohomologySum (k := k) X Y n ≃ₗ[k]
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) (TopCat.of (X × Y)) n :=
  (CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y n).trans
    (((productHomotopyEquiv (k := k) X Y).toHomologyIso n).toLinearEquiv.trans
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X)
        (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) n).symm).dualMap |>.trans
      (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) n).symm

/-- Each tensor generator maps to the cup of the two actual projection pullbacks. -/
theorem canonicalCohomologyEquiv_lof_add (p q : ℕ)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y q) :
    canonicalCohomologyEquiv X Y (p + q)
      (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
        (fun ij => Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X ij.val.1 ⊗[k]
          Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y ij.val.2) ⟨(p, q), rfl⟩ (a ⊗ₜ[k] b)) =
      Products.CupCohomology.singularCohomologyCup (TopCat.of (X × Y)) p q
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k) TopCat.prodFst p a)
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of k k) TopCat.prodSnd q b) := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.singularCochains (ModuleCat.of k k) X) p a
  obtain ⟨d, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.singularCochains (ModuleCat.of k k) Y) q b
  apply (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) (p + q)).injective
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (CohomologyTensorLof.Construction.CohomologyTensorNormalization.cocycleTensorFunctional_comp_algebraic X Y p q c d)
    ((TensorHomologyD.Construction.TensorHomology.algebraicKunneth (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X)
      (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) (p + q)).symm
      (HomologicalComplex.homologyMap (TensorAlexanderWhitney.Construction.ProductAlexanderWhitney.productAw k (X, Y)) (p + q) z))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  change Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) (p + q)
    ((Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (TopCat.of (X × Y)) (p + q)).symm _) z = _
  rw [LinearEquiv.apply_symm_apply]
  exact h.symm.trans (CupHomologyComparison.cup_tensor_homology k (X, Y) p q c d z)

end Construction.CanonicalCohomologyKunneth

end

end OAI.AlgebraicTopology.Kunneth.CanonicalCohomology
