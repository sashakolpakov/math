import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreePieces
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor Graded Action -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorGradedAction.GradedModules

noncomputable section

/-! Tensoring a graded module with an arbitrary coefficient module preserves the original graded polynomial action. -/

open TensorProduct DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
variable (S : Type t) [AddCommGroup S] [Module R S]

omit [GradedAlgebra 𝒜] in
theorem decomposeTensor_gradedSMul : SetLike.GradedSMul 𝒜 (decomposeTensor ℳ S) := by
  constructor
  intro i j a x ha hx
  change a • x ∈ decomposeTensor ℳ S (i + j)
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.inductionOn with
  | tmul m s =>
    refine ⟨(⟨a • m.val, SetLike.GradedSMul.smul_mem ha m.property⟩ : ℳ (i + j)) ⊗ₜ[R] s, ?_⟩
    rfl
  | add y z hy hz =>
    simp only [map_add, smul_add]
    exact Submodule.add_mem _ hy hz

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorGradedAction.GradedModules
