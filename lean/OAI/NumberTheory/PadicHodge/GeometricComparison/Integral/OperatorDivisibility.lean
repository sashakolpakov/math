import Mathlib.Algebra.Module.LinearMap.Basic

/-! # Operator Divisibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OperatorDivisibility.IntegralOperatorDivisibility

/-! Vanishing of the composite reduction of an integral operator gives
divisibility whenever the original reduction detects scalar multiples. -/

variable {R V W N : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup N] [Module R N]

theorem divisible (e : V →ₗ[R] W) (r : W →ₗ[R] N) (F : V →ₗ[R] V) (s : R)
    (h : ∀ z, r (e z) = 0 ↔ ∃ y, z = s • y) (x : V)
    (hz : (r.comp (e.comp F)) x = 0) : ∃ y, F x = s • y :=
  (h (F x)).mp hz

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.OperatorDivisibility.IntegralOperatorDivisibility
