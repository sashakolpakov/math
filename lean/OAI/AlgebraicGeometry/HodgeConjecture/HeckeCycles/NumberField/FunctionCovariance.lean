import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.PureHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction

/-! # Function Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionCovariance.CM

noncomputable section

/-! Concrete local Heisenberg covariance descends to the actual global
Schwartz functions through the proved restricted-tensor evaluation map. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (hψ : ψ = AdelicCharacter.CM.character F)
  {G : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F → Type*} [∀ v, Group (G v)]
  (K : ∀ v, Subgroup (G v))
  (ρ : ∀ v, G v →* (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N ≃ₗ[ℂ]
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N))
  (hρ : ∀ᶠ v in cofinite, ∀ g ∈ K v, ρ v g (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v)
  (g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K) (z w : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
  (hlocal : ∀ v f,
    ρ v (g v) (HeisenbergFamily.CM.Family.localOperator F N ψ hu hc z v f) =
      HeisenbergFamily.CM.Family.localOperator F N ψ hu hc w v (ρ v (g v) f))

include hψ hlocal in
theorem pure_covariance
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    Finite.FunctionAction.CM.functionAction F N K ρ hρ g
      (Finite.TraceHeisenberg.CM.operator F N (fun i => z (.inr i)) (fun i => z (.inl i))
        (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))) =
      Finite.TraceHeisenberg.CM.operator F N (fun i => w (.inr i)) (fun i => w (.inl i))
        (Finite.FunctionAction.CM.functionAction F N K ρ hρ g
          (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf))) := by
  rw [← PureHeisenberg.CM.evaluation F N ψ hu hc hψ z f hf]
  rw [Finite.FunctionAction.CM.intertwines, Finite.FunctionAction.CM.intertwines,
    RestrictedTensorExpansion.CM.action_pure]
  rw [← PureHeisenberg.CM.evaluation F N ψ hu hc hψ w]
  unfold PureHeisenberg.CM.translated
  rw [RestrictedTensorExpansion.CM.action_pure]
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) _ _) x =
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) _ _) x
  rw [RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure]
  apply finprod_congr
  intro v
  exact congrArg (fun φ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N => φ.val (fun i => x i v))
    (hlocal v (f v))

include hψ hlocal in
theorem covariance (φ : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N) :
    Finite.FunctionAction.CM.functionAction F N K ρ hρ g
      (Finite.TraceHeisenberg.CM.operator F N (fun i => z (.inr i)) (fun i => z (.inl i)) φ) =
      Finite.TraceHeisenberg.CM.operator F N (fun i => w (.inr i)) (fun i => w (.inl i))
        (Finite.FunctionAction.CM.functionAction F N K ρ hρ g φ) := by
  have h := Finite.PureFunctionExt.CM.ext F N
    ((Finite.FunctionAction.CM.functionAction F N K ρ hρ g).toLinearMap.comp
      (Finite.TraceHeisenberg.CM.operator F N (fun i => z (.inr i)) (fun i => z (.inl i))).toLinearMap)
    ((Finite.TraceHeisenberg.CM.operator F N (fun i => w (.inr i)) (fun i => w (.inl i))).toLinearMap.comp
      (Finite.FunctionAction.CM.functionAction F N K ρ hρ g).toLinearMap)
    (pure_covariance F N ψ hu hc hψ K ρ hρ g z w hlocal)
  exact congrArg (fun T : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N →ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions F N => T φ) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FunctionCovariance.CM
