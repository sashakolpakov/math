import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Tensor Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TensorLattice

noncomputable section

/-! A finite integral basis makes its image a full lattice in the scalar
extension. This applies to the constructed Tate bases. -/

open scoped TensorProduct

variable {R K M I : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup M] [Module R M] [Fintype I]

theorem tensorIntegralImage_isLattice (b : Module.Basis I R M) :
    Submodule.IsLattice K (TensorProduct.mk R K M 1).range := by
  have : Module.Finite R M := Module.Finite.of_basis b
  constructor
  · exact Submodule.fg_range _
  · apply top_unique
    rw [← (b.baseChange K).span_eq]
    apply Submodule.span_mono
    rintro z ⟨i, rfl⟩
    exact ⟨b i, (Module.Basis.baseChange_apply K b i).symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TensorLattice
