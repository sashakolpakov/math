import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Injective Coefficient Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveCoefficientDuality

noncomputable section

/-! Dualization into an injective coefficient ring is exact. In particular,
this applies to the genuine finite Witt coefficient rings. -/

universe u

variable {R : Type u} [CommRing R] [Module.Injective R R]
  {M N P : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

theorem dualMap_surjective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Surjective f.dualMap := by
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.out f hf φ
  exact ⟨ψ, LinearMap.ext hψ⟩

theorem range_dualMap (f : M →ₗ[R] N) :
    LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f
    (dualMap_surjective (LinearMap.range f).subtype Subtype.val_injective)

theorem dual_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range, range_dualMap,
    LinearMap.exact_iff.mp h]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveCoefficientDuality
