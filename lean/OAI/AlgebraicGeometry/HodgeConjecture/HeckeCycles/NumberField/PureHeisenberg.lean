import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergProduct
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PureFunctionExt

/-! # Pure Heisenberg -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.PureHeisenberg.CM

noncomputable section

/-! The actual number-field Heisenberg action on Schwartz functions is
the evaluation of the restricted tensor of actual local translates. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
  (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (hψ : ψ = AdelicCharacter.CM.character F)

def translated (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (fun v => HeisenbergFamily.CM.Family.localOperator F N ψ hu hc z v (f v))
    (HeisenbergFamily.CM.Family.family_restricted F N ψ hu hc z f hf)

include hψ in
theorem evaluation (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (translated F N ψ hu hc z f hf) =
      Finite.TraceHeisenberg.CM.operator F N (fun i => z (.inr i)) (fun i => z (.inl i))
        (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz F N (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf)) := by
  apply Subtype.ext
  funext x
  change RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F N (translated F N ψ hu hc z f hf) x = _
  rw [Finite.TraceHeisenberg.CM.operator_apply]
  unfold translated
  rw [RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure, HeisenbergProduct.CM.product F N ψ hu hc z f hf x]
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.heisenberg
  rw [hψ, LocalCharacter.CM.constructed_finite]
  congr 1
  exact (RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction_pure F N f hf _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.PureHeisenberg.CM
