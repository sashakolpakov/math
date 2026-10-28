import OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney

/-! # Cohomology Tensor Lof -/

namespace OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof

noncomputable section

/-! Normalize the dual decomposition by actual cohomology evaluations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace Construction.CohomologyTensorNormalization

open OAI.AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.CohomologyDecomposition OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorCocycles

variable {k : Type} [Field k]

section DirectSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)]

theorem directSumDualEquiv_lof_self (i : ι) (f : Module.Dual k (M i)) (x : M i) :
    CohomologyTensorNe.Construction.CohomologyDecomposition.directSumDualEquiv M (DirectSum.lof k ι (fun j => Module.Dual k (M j)) i f)
      (DirectSum.lof k ι M i x) = f x := by
  change DFinsupp.lsum k
    (DirectSum.linearEquivFunOnFintype k ι (fun j => Module.Dual k (M j))
      (DirectSum.lof k ι (fun j => Module.Dual k (M j)) i f))
    (DFinsupp.single i x) = _
  rw [DirectSum.linearEquivFunOnFintype_lof, DFinsupp.lsum_single]
  simp only [Pi.single_eq_same]

theorem directSumDualEquiv_lof_other (i j : ι) (h : j ≠ i)
    (f : Module.Dual k (M i)) (x : M j) :
    CohomologyTensorNe.Construction.CohomologyDecomposition.directSumDualEquiv M (DirectSum.lof k ι (fun j => Module.Dual k (M j)) i f)
      (DirectSum.lof k ι M j x) = 0 := by
  change DFinsupp.lsum k
    (DirectSum.linearEquivFunOnFintype k ι (fun j => Module.Dual k (M j))
      (DirectSum.lof k ι (fun j => Module.Dual k (M j)) i f))
    (DFinsupp.single j x) = _
  rw [DirectSum.linearEquivFunOnFintype_lof, DFinsupp.lsum_single]
  simp only [Pi.single_eq_of_ne h, LinearMap.zero_apply]

end DirectSum

theorem cocycleDual_closed (K : SSet.{0}) (p : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of k k)) p) :
    (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of k k) p c.val).comp
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).d (p + 1) p).hom = 0 := by
  apply LinearMap.ext
  intro z
  exact Cohomology.Singular.Evaluation.cocycle_evaluation_boundary K (ModuleCat.of k k) p (p + 1) c z

theorem cocycleDual_representatives (K : SSet.{0}) (p : ℕ)
    (c : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of k k)) p)
    (u : (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K).homology p) :
    Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of k k) p c.val
        (ChainSplittingD.Construction.ChainSplitting.representatives (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) p u).val =
      Cohomology.Singular.UniversalCoefficient.simplicialUniversalCoefficientEquiv K p
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of k k)) p c) u := by
  have h := Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class K (ModuleCat.of k k) p c
    (ChainSplittingD.Construction.ChainSplitting.representatives (Cohomology.Singular.ChainDual.simplicialScalarChains (R := k) K) p u)
  rw [ChainSplittingD.Construction.ChainSplitting.class_representatives] at h
  exact h.symm

def cocycleTensorFunctional (X Y : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) X p)
    (d : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) Y q) :
    Module.Dual k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X ⊗ Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology (p + q)) :=
  TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X) (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) p q
    (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of k k) p c.val)
    (Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj Y) (ModuleCat.of k k) q d.val)
    (cocycleDual_closed (TopCat.toSSet.obj X) p c) (cocycleDual_closed (TopCat.toSSet.obj Y) q d)

variable (X Y : TopCat.{0})
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology n)]
variable [∀ n, FiniteDimensional k ((Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology n)]

theorem cohomologySumDualEquiv_lof (n : ℕ) (ij : TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X ij.val.1)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y ij.val.2) :
    CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y n
      (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs n)
        (fun d => Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X d.val.1 ⊗[k]
          Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y d.val.2) ij (a ⊗ₜ[k] b)) =
      CohomologyTensorNe.Construction.CohomologyDecomposition.directSumDualEquiv
        (fun d : TensorHomologyD.Construction.TensorHomology.DegreePairs n =>
          (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X).homology d.val.1 ⊗[k]
            (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y).homology d.val.2)
        (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs n) _ ij
          (TensorAlexanderWhitney.Construction.TensorCocycles.pairing (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X ij.val.1 a)
            (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv Y ij.val.2 b))) := by
  simp only [CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv, LinearEquiv.trans_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, LinearEquiv.coe_coe,
    TensorProduct.congr_tmul]
  simp only [← LinearEquiv.coe_coe, TensorProduct.toLinearMap_dualDistribEquiv, TensorAlexanderWhitney.Construction.TensorCocycles.pairing]

theorem cocycleTensorFunctional_comp_algebraic (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) X p)
    (d : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of k k) Y q) :
    (cocycleTensorFunctional X Y p q c d).comp
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X)
        (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) (p + q)).toLinearMap =
      CohomologyTensorNe.Construction.CohomologyDecomposition.cohomologySumDualEquiv X Y (p + q)
        (DirectSum.lof k (TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
          (fun ij => Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) X ij.val.1 ⊗[k]
            Cohomology.Singular.Basic.singularCohomology (ModuleCat.of k k) Y ij.val.2) ⟨(p, q), rfl⟩
          (Cohomology.Singular.Representatives.singularClass (ModuleCat.of k k) X p c ⊗ₜ[k]
            Cohomology.Singular.Representatives.singularClass (ModuleCat.of k k) Y q d)) := by
  rw [cohomologySumDualEquiv_lof]
  apply DirectSum.linearMap_ext
  intro ij
  apply TensorProduct.ext'
  intro u v
  by_cases hij : ij = (⟨(p, q), rfl⟩ : TensorHomologyD.Construction.TensorHomology.DegreePairs (p + q))
  · subst ij
    change TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X)
      (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) p q _ _ _ _
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth _ _ (p + q) (DirectSum.lof k _ _ _ (u ⊗ₜ[k] v))) = _
    rw [TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_algebraic_self]
    simp only [LinearMap.comp_apply]
    rw [directSumDualEquiv_lof_self, TensorAlexanderWhitney.Construction.TensorCocycles.pairing_tmul,
      cocycleDual_representatives, cocycleDual_representatives]
    rfl
  · change TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional (Cohomology.Singular.Evaluation.singularScalarChains (R := k) X)
      (Cohomology.Singular.Evaluation.singularScalarChains (R := k) Y) p q _ _ _ _
      (TensorHomologyD.Construction.TensorHomology.algebraicKunneth _ _ (p + q) (DirectSum.lof k _ _ ij (u ⊗ₜ[k] v))) = _
    rw [TensorAlexanderWhitney.Construction.TensorCocycles.tensorHomologyFunctional_algebraic_other _ _ _ _ _ _ _ _ ij hij]
    simp only [LinearMap.comp_apply]
    rw [directSumDualEquiv_lof_other _ _ ij hij]

end Construction.CohomologyTensorNormalization

end

end OAI.AlgebraicTopology.Kunneth.CohomologyTensorLof
