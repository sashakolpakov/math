import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Functional Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctionalLift

noncomputable section

/-! Scalar-valued functionals on a coefficient extension of a projective module lift across a surjective coefficient map. The lifted functional agrees with the original one on the full tensor product. -/

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R] {K : Type v} [CommRing K] [Algebra R K]
variable {M : Type w} [AddCommGroup M] [Module R M]

theorem scalarFunctional_exists_lift [Module.Projective R M]
    (hs : Function.Surjective (algebraMap R K)) (f : K ⊗[R] M →ₗ[K] K) :
    ∃ l : M →ₗ[R] R, ∀ x, algebraMap R K (l x) = f (1 ⊗ₜ[R] x) := by
  let g := (f.restrictScalars R).comp (TensorProduct.mk R K M 1)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap R K) g hs
  exact ⟨l, fun x => LinearMap.congr_fun hl x⟩

theorem scalarFunctional_lift_tensor_identity (f : K ⊗[R] M →ₗ[K] K) (l : M →ₗ[R] R)
    (h : ∀ x, algebraMap R K (l x) = f (1 ⊗ₜ[R] x)) :
    (TensorProduct.rid R K).toLinearMap.comp (l.lTensor K) = f.restrictScalars R := by
  ext a x
  change l x • a = f (a ⊗ₜ[R] x)
  rw [Algebra.smul_def, h x, mul_comm]
  have H := f.map_smul a (1 ⊗ₜ[R] x)
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using H.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctionalLift
