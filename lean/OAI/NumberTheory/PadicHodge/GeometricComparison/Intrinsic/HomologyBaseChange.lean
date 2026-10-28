import OAI.NumberTheory.PadicHodge.GeometricComparison.HomologyScalarExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtensionTensorEquivalence

/-! # Homology Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HomologyBaseChange.ChainScalarExtension

noncomputable section

/-! The actual tensor base-change equivalence on singular homology is natural for continuous maps. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (R S : Type) [Field R] [Field S] [Algebra R S]

def tensorHomologyEquiv (X : TopCat.{0}) (n : ℕ) :
    (S ⊗[R] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) ≃ₗ[S]
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := S) X).homology n :=
  (ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)).symm.trans
    (HomologyScalarExtension.ChainScalarExtension.homologyIso (algebraMap R S) X n).toLinearEquiv

theorem tensorHomologyEquiv_obj_apply (X : TopCat.{0}) (n : ℕ)
    (a : (HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).obj ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)) :
    tensorHomologyEquiv R S X n (ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv _ a) = (HomologyScalarExtension.ChainScalarExtension.homologyIso (algebraMap R S) X n).hom a := by
  change (HomologyScalarExtension.ChainScalarExtension.homologyIso (algebraMap R S) X n).hom
    ((ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv _).symm ((ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv _) a)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem tensorHomologyEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (x : S ⊗[R] (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) :
    tensorHomologyEquiv R S Y n
        ((HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) n).hom.baseChange S x) =
      (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := S) f) n)
        (tensorHomologyEquiv R S X n x) := by
  obtain ⟨a, rfl⟩ := (ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n)).surjective x
  rw [← ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv_naturality]
  change (HomologyScalarExtension.ChainScalarExtension.homologyIso (algebraMap R S) Y n).hom
      ((ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y).homology n)).symm
        ((ExtensionTensorEquivalence.ChainScalarExtension.tensorObjEquiv ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y).homology n))
          ((HomologyScalarExtension.ChainScalarExtension.extension (algebraMap R S)).map
            (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f) n) a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rw [tensorHomologyEquiv_obj_apply]
  exact ConcreteCategory.congr_hom (HomologyScalarExtension.ChainScalarExtension.homologyIso_naturality (algebraMap R S) f n) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HomologyBaseChange.ChainScalarExtension
