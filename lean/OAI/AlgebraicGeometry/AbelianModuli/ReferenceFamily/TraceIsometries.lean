import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reconstruction

/-! # Trace Isometries -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries.TraceReconstruction

noncomputable section

/-! The trace construction commutes with actual E-linear maps and
identifies their rational polarization and Hermitian isometries. -/

variable {E V W : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]
  [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

theorem coefficient_isometry (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (φ : W →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (f : V →ₗ[E] W) (hf : ∀ x y, φ (f x) (f y) = ψ x y) (x y : V) :
    TraceReconstructionEq.TraceReconstruction.coefficient (E := E) φ (f x) (f y) = TraceReconstructionEq.TraceReconstruction.coefficient ψ x y := by
  apply TraceReconstructionEq.TraceReconstruction.coefficient_eq_of_trace
  intro a
  rw [TraceReconstructionEq.TraceReconstruction.coefficient_spec, ← f.map_smul, hf]

theorem hermitianCoefficient_isometry_iff (ξ : E) (hξ : ξ ≠ 0)
    (ψ : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (φ : W →ₗ[ℚ] W →ₗ[ℚ] ℚ) (f : V →ₗ[E] W) :
    (∀ x y, Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient ξ φ (f x) (f y) = Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient ξ ψ x y) ↔
      ∀ x y, φ (f x) (f y) = ψ x y := by
  constructor
  · intro hf x y
    rw [← Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient_trace ξ hξ φ (f x) (f y), hf,
      Hermitian.Reconstruction.TraceReconstruction.hermitianCoefficient_trace ξ hξ ψ x y]
  · intro hf x y
    exact congrArg (fun a : E => ξ⁻¹ * a) (coefficient_isometry ψ φ f hf x y)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TraceIsometries.TraceReconstruction
