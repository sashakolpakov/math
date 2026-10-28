import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.LocalCharacter
import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

/-! # Heisenberg Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily.CM.Family

noncomputable section

/-! Every actual finite-adelic phase defines a restricted family of
local Heisenberg operators. The integral vacuum is fixed almost everywhere. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : CharZero (v.adicCompletion F) := RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

theorem vacuum_indicator (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val =
      IntegralHeisenberg.CM.indicator (v.adicCompletionIntegers F).toSubring := by
  funext x
  change Set.indicator (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice F N v) (fun _ => (1 : ℂ)) x = _
  simp only [Set.indicator, RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finitePositionLattice, Set.mem_pi, Set.mem_univ, forall_true_left,
    IntegralHeisenberg.CM.indicator]
  rfl

variable (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)

def localOperator (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N ≃ₗ[ℂ] RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N :=
  IntegralHeisenberg.CM.operator (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v))
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v)) (fun i => z i v)

theorem half_integral : ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite,
    (2 : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h := Sum.inr_injective.tendsto_cofinite.eventually (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F ((2 : F)⁻¹))
  filter_upwards [h] with v hv
  change RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) ((2 : F)⁻¹) ∈ v.adicCompletionIntegers F at hv
  simpa only [map_inv₀, map_ofNat] using hv

theorem local_unramified (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∀ᶠ v in cofinite, localOperator F N ψ hu hc z v (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  have hz : ∀ᶠ v in cofinite, ∀ i, z i v ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.mpr (fun i => (z i).property)
  filter_upwards [hz, half_integral F,
    RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc] with v hv hh hψ
  apply Subtype.ext
  change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) (fun i => z i v)
    (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val = (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v).val
  rw [vacuum_indicator]
  exact IntegralHeisenberg.CM.fixed (v.adicCompletionIntegers F).toSubring
    (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) hψ hh (fun i => z i v) hv

theorem family_restricted (z : (Fin N ⊕ Fin N) → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    ∀ᶠ v in cofinite, localOperator F N ψ hu hc z v (f v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  filter_upwards [hf, local_unramified F N ψ hu hc z] with v hv h
  rw [hv, h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.HeisenbergFamily.CM.Family
