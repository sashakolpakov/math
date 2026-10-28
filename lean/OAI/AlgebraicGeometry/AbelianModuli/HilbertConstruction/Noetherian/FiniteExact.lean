import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Noetherian.Basic

/-! # Finite Exact -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact

/-! Over a Noetherian coefficient ring, an exact pair with finite outside modules has a finite middle module. -/

universe u

theorem noetherian_finite_of_exact {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    [Module.Finite R M] [Module.Finite R P] (h : Function.Exact f g) : Module.Finite R N := by
  have : IsNoetherian R N :=
    isNoetherian_of_range_eq_ker f g (LinearMap.exact_iff.mp h).symm
  infer_instance

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact
