import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingOf
import Mathlib.Tactic.Module

/-! # Equation Periodic Complex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicComplex.BundleCycles

noncomputable section

/-!
# LineBundleCycles: periodic multiplication by two annihilating factors
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem equationPeriodic_comp_zero (a b : R) (h : ∀ m : M, (a * b) • m = 0) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism b M).comp (MultiplicationSequence.BundleCycles.equationEndomorphism a M) = 0 := by
  apply LinearMap.ext
  intro m
  change b • (a • m) = 0
  rw [← mul_smul, mul_comm b a]
  exact h m

theorem equationPeriodic_kill_swap (a b : R) (h : ∀ m : M, (a * b) • m = 0) :
    ∀ m : M, (b * a) • m = 0 := by
  simpa only [mul_comm b a] using h

def equationPeriodicComplex (a b : R) (h : ∀ m : M, (a * b) • m = 0) :
    HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape :=
  Periodic.PeriodicComplex.BundleCycles.endomorphismPeriodicComplex (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism b M)
    (equationPeriodic_comp_zero a b h)
    (equationPeriodic_comp_zero b a (equationPeriodic_kill_swap a b h))

theorem equationPeriodicEulerLength_swap (a b : R)
    (h : ∀ m : M, (a * b) • m = 0)
    (h₀ : Module.length R ((equationPeriodicComplex a b h).homology false) ≠ ⊤)
    (h₁ : Module.length R ((equationPeriodicComplex a b h).homology true) ≠ ⊤)
    (h₀' : Module.length R ((equationPeriodicComplex b a
      (equationPeriodic_kill_swap a b h)).homology false) ≠ ⊤)
    (h₁' : Module.length R ((equationPeriodicComplex b a
      (equationPeriodic_kill_swap a b h)).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (equationPeriodicComplex b a (equationPeriodic_kill_swap a b h)) h₀' h₁' =
      -Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (equationPeriodicComplex a b h) h₀ h₁ :=
  Periodic.ScalingOf.BundleCycles.periodicEulerLength_swap _ _ _ _ h₀ h₁ h₀' h₁'

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.EquationPeriodicComplex.BundleCycles
