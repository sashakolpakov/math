import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceReconstructionEq
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

/-! # Reconstruction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction.TraceReconstruction

noncomputable section

/-! The trace coefficients of an alternating rational form satisfying
the CM adjoint equation reconstruct an actual Hermitian form. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

variable {E V : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]

def RosatiBalanced (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) : Prop :=
  ∀ (a : E) (x y : V), ψ (a • x) y = ψ x (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a • y)

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Module E V] [IsScalarTower ℚ E V] in
theorem skew_of_alternating (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hψ : ∀ x, ψ x x = 0) (x y : V) :
    ψ y x = -ψ x y := by
  have h := hψ (x + y)
  simp only [map_add, LinearMap.add_apply, hψ] at h
  linarith

theorem coefficient_smul_right (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hψ : RosatiBalanced (E := E) ψ)
    (a : E) (x y : V) : TraceReconstructionEq.TraceReconstruction.coefficient ψ x (a • y) = ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a * TraceReconstructionEq.TraceReconstruction.coefficient ψ x y := by
  apply TraceReconstructionEq.TraceReconstruction.coefficient_eq_of_trace
  intro b
  calc
    Algebra.trace ℚ E ((ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a * TraceReconstructionEq.TraceReconstruction.coefficient ψ x y) * b) =
        Algebra.trace ℚ E (TraceReconstructionEq.TraceReconstruction.coefficient ψ x y * (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a * b)) :=
      congrArg (Algebra.trace ℚ E) (by ring)
    _ = ψ ((ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a * b) • x) y := TraceReconstructionEq.TraceReconstruction.coefficient_spec ψ x y _
    _ = ψ (b • x) (a • y) := by
      rw [mul_smul, hψ, ComplexMultiplication.CM.TraceForm.cmFieldConjugation_involutive]

theorem coefficient_conjugate (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hψ : RosatiBalanced (E := E) ψ) (hAlt : ∀ x, ψ x x = 0) (x y : V) :
    TraceReconstructionEq.TraceReconstruction.coefficient (E := E) ψ y x = -ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (TraceReconstructionEq.TraceReconstruction.coefficient ψ x y) := by
  apply TraceReconstructionEq.TraceReconstruction.coefficient_eq_of_trace
  intro a
  calc
    Algebra.trace ℚ E ((-ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (TraceReconstructionEq.TraceReconstruction.coefficient ψ x y)) * a) =
        -Algebra.trace ℚ E (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (TraceReconstructionEq.TraceReconstruction.coefficient ψ x y * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a)) := by
      rw [map_mul (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E), ComplexMultiplication.CM.TraceForm.cmFieldConjugation_involutive, neg_mul, map_neg]
    _ = -Algebra.trace ℚ E (TraceReconstructionEq.TraceReconstruction.coefficient ψ x y * ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a) :=
      congrArg (fun q : ℚ => -q) (Algebra.trace_eq_of_algEquiv (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E) _)
    _ = -ψ (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a • x) y :=
      congrArg (fun q : ℚ => -q) (TraceReconstructionEq.TraceReconstruction.coefficient_spec ψ x y _)
    _ = -ψ x (a • y) := by rw [hψ, ComplexMultiplication.CM.TraceForm.cmFieldConjugation_involutive]
    _ = ψ (a • y) x := (skew_of_alternating ψ hAlt x (a • y)).symm

def hermitianCoefficient (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) : E :=
  ξ⁻¹ * TraceReconstructionEq.TraceReconstruction.coefficient ψ x y

omit [NumberField.IsCMField E] in
theorem hermitianCoefficient_add_left (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x z y : V) :
    hermitianCoefficient ξ ψ (x + z) y =
      hermitianCoefficient ξ ψ x y + hermitianCoefficient ξ ψ z y := by
  simp only [hermitianCoefficient, TraceReconstructionEq.TraceReconstruction.coefficient_add_left, mul_add]

omit [NumberField.IsCMField E] in
theorem hermitianCoefficient_add_right (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y z : V) :
    hermitianCoefficient ξ ψ x (y + z) =
      hermitianCoefficient ξ ψ x y + hermitianCoefficient ξ ψ x z := by
  simp only [hermitianCoefficient, TraceReconstructionEq.TraceReconstruction.coefficient_add_right, mul_add]

omit [NumberField.IsCMField E] in
theorem hermitianCoefficient_trace (ξ : E) (hξ : ξ ≠ 0)
    (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (x y : V) :
    Algebra.trace ℚ E (ξ * hermitianCoefficient ξ ψ x y) = ψ x y := by
  rw [hermitianCoefficient, ← mul_assoc, mul_inv_cancel₀ hξ, one_mul]
  exact TraceReconstructionEq.TraceReconstruction.coefficient_trace ψ x y

theorem hermitianCoefficient_symmetry (ξ : E) (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ)
    (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hψ : RosatiBalanced (E := E) ψ)
    (hAlt : ∀ x, ψ x x = 0) (x y : V) :
    ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (hermitianCoefficient ξ ψ x y) = hermitianCoefficient ξ ψ y x := by
  rw [hermitianCoefficient, hermitianCoefficient, map_mul (ComplexMultiplication.CM.TraceForm.cmFieldConjugation E),
    map_inv₀, hξ, inv_neg, coefficient_conjugate ψ hψ hAlt x y]
  ring

omit [NumberField.IsCMField E] in
theorem hermitianCoefficient_smul_left (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (a : E) (x y : V) :
    hermitianCoefficient ξ ψ (a • x) y = a * hermitianCoefficient ξ ψ x y := by
  rw [hermitianCoefficient, hermitianCoefficient, TraceReconstructionEq.TraceReconstruction.coefficient_smul_left]
  ring

theorem hermitianCoefficient_smul_right (ξ : E) (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hψ : RosatiBalanced (E := E) ψ) (a : E) (x y : V) :
    hermitianCoefficient ξ ψ x (a • y) = ComplexMultiplication.CM.TraceForm.cmFieldConjugation E a * hermitianCoefficient ξ ψ x y := by
  rw [hermitianCoefficient, hermitianCoefficient, coefficient_smul_right ψ hψ]
  ring

omit [NumberField.IsCMField E] in
theorem hermitianCoefficient_nondegenerate (ξ : E) (hξ : ξ ≠ 0)
    (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hψ : ∀ x, (∀ y, ψ x y = 0) → x = 0)
    (x : V) (hx : ∀ y, hermitianCoefficient ξ ψ x y = 0) : x = 0 := by
  apply hψ x
  intro y
  exact (hermitianCoefficient_trace ξ hξ ψ x y).symm.trans
    ((congrArg (fun a => Algebra.trace ℚ E (ξ * a)) (hx y)).trans (by rw [mul_zero, map_zero]))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction.TraceReconstruction
