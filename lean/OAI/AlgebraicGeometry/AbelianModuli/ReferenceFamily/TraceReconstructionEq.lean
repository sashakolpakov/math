import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Trace Reconstruction Eq -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceReconstructionEq.TraceReconstruction

noncomputable section

/-! Reconstruct E-valued coefficients from a rational bilinear form
using the nondegenerate trace pairing. This is the linear-algebra step
needed to recover the Hermitian form of a marked PEL polarization. -/

variable {E V : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]

def traceDual : E ≃ₗ[ℚ] Module.Dual ℚ E :=
  (Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)

def coefficientFunctional (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) : E →ₗ[ℚ] ℚ where
  toFun a := ψ (a • x) y
  map_add' a b := by simp only [add_smul, map_add, LinearMap.add_apply]
  map_smul' q a := by simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply]

def coefficient (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) : E :=
  traceDual.symm (coefficientFunctional ψ x y)

theorem coefficient_spec (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) (a : E) :
    Algebra.trace ℚ E (coefficient ψ x y * a) = ψ (a • x) y :=
  LinearMap.BilinForm.apply_toDual_symm_apply (B := Algebra.traceForm ℚ E)
    (hB := traceForm_nondegenerate ℚ E) (coefficientFunctional ψ x y) a

theorem coefficient_trace (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) :
    Algebra.trace ℚ E (coefficient ψ x y) = ψ x y := by
  simpa only [mul_one, one_smul] using coefficient_spec ψ x y (1 : E)

theorem coefficient_eq_of_trace (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) (u : E)
    (hu : ∀ a : E, Algebra.trace ℚ E (u * a) = ψ (a • x) y) : coefficient ψ x y = u := by
  apply (traceDual (E := E)).injective
  apply LinearMap.ext
  intro a
  exact (coefficient_spec ψ x y a).trans (hu a).symm

theorem coefficient_smul_left (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (a : E) (x y : V) :
    coefficient ψ (a • x) y = a * coefficient ψ x y := by
  apply coefficient_eq_of_trace
  intro b
  calc
    Algebra.trace ℚ E ((a * coefficient ψ x y) * b) =
        Algebra.trace ℚ E (coefficient ψ x y * (b * a)) := congrArg (Algebra.trace ℚ E) (by ring)
    _ = ψ ((b * a) • x) y := coefficient_spec ψ x y (b * a)
    _ = ψ (b • (a • x)) y := by rw [mul_smul]

theorem coefficient_add_left (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x z y : V) :
    coefficient (E := E) ψ (x + z) y = coefficient ψ x y + coefficient ψ z y := by
  apply coefficient_eq_of_trace
  intro a
  rw [add_mul, map_add, coefficient_spec (E := E), coefficient_spec (E := E),
    smul_add, map_add, LinearMap.add_apply]

theorem coefficient_add_right (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y z : V) :
    coefficient (E := E) ψ x (y + z) = coefficient ψ x y + coefficient ψ x z := by
  apply coefficient_eq_of_trace
  intro a
  rw [add_mul, map_add, coefficient_spec (E := E), coefficient_spec (E := E), map_add]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceReconstructionEq.TraceReconstruction
