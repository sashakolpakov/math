import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ProductRelations
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedTensorExpansion

/-! # Evaluation Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationKernel.CM

noncomputable section

/-! The kernel of actual restricted-tensor evaluation is invariant under
the constructed local actions. This proves descent to actual functions. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation
open OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  {G : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F → Type*} [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (G v))
  (ρ : ∀ v, G v →* (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N ≃ₗ[ℂ]
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N))
  (hρ : ∀ᶠ v in cofinite, ∀ g ∈ K v, ρ v g (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)

include hρ in
theorem action_preserves_zero (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (x : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N)
    (hx : RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N x = 0) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) K ρ hρ g x) = 0 := by
  obtain ⟨r, c, f, hf, hrep⟩ := RestrictedTensorExpansion.CM.expansion (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) x
  have hT : ∀ᶠ v in cofinite, ρ v (g v) (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
    filter_upwards [hρ, g.property] with v hv hg
    exact hv (g v) hg
  have hz (z : Fin N → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
      ∑ j, c j * ∏ᶠ v, (f j v).val (fun i => z i v) = 0 := by
    have h := congrFun hx z
    rw [hrep] at h
    simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, Pi.zero_apply] using h
  funext y
  have ht := ProductRelations.CM.relation_preserved F N
    (fun v => (ρ v (g v)).toLinearMap) hT c f hf hz y
  rw [hrep]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    RestrictedTensorExpansion.CM.action_pure, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, Pi.zero_apply]
  exact ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationKernel.CM
