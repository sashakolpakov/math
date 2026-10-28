import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IntegralHeisenberg
import OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator

/-! # Heisenberg Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.HeisenbergCovariance.CM

noncomputable section

/-! Actual local oscillator operators intertwine the concrete
Heisenberg operators, directly from their defining graph condition. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [CharZero k] [NonarchimedeanAddGroup k]
  {N : ℕ} (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)

theorem covariance (g : RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (v : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g (IntegralHeisenberg.CM.operator ψ hu hc v f) =
      IntegralHeisenberg.CM.operator ψ hu hc
        (RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ g) v) (RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ g f) := by
  apply Subtype.ext
  exact (g.property.2 v f (IntegralHeisenberg.CM.operator ψ hu hc v f)).mp rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.HeisenbergCovariance.CM
