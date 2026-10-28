import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Scalar Left Inverse -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ScalarLeftInverse

noncomputable section

/-! A left inverse up to a nonzero scalar proves injectivity even after
a non-flat extension of scalars into a domain. -/

open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
  {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

theorem injective [Module.Free R A]
    (f : A →ₗ[R] B) (u : B →ₗ[R] A) (r : R)
    (hr : algebraMap R S r ≠ 0) (h : u.comp f = r • LinearMap.id) :
    Function.Injective (f.baseChange S) := by
  have he : (u.baseChange S).comp (f.baseChange S) = r • LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  intro x y hxy
  have hu := congrArg (u.baseChange S) hxy
  change ((u.baseChange S).comp (f.baseChange S)) x =
    ((u.baseChange S).comp (f.baseChange S)) y at hu
  rw [he] at hu
  change r • x = r • y at hu
  rw [← algebraMap_smul S r x, ← algebraMap_smul S r y] at hu
  exact smul_right_injective _ hr hu

theorem scalar_injective [Module.Free R A] (f : A →ₗ[R] A) (r : R)
    (hr : algebraMap R S r ≠ 0) (h : f = r • LinearMap.id) :
    Function.Injective (f.baseChange S) := by
  apply injective R S f LinearMap.id r hr
  simpa only [LinearMap.id_comp] using h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ScalarLeftInverse
