/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import Mathlib
import SphericalReggeScissors.ReggeMatrix

/-!
# Four-channel bilinear cancellation

This is the algebraic kernel of the manuscript's coproduct calculation.
It is stated for an arbitrary bilinear map over `ℚ`; taking that map to be
the canonical map into a tensor product gives exactly the required tensor
identity.  Thus no fact about motives or scissors groups enters this file.
-/

namespace SphericalReggeScissors

open scoped TensorProduct

section Bilinear

variable {M N P : Type*}
  [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]
  [AddCommGroup P] [Module ℚ P]

/-- The integral Hadamard transform of a four-tuple. -/
def hadamardTransform (v : Four → M) : Four → M :=
  fun i => ∑ j, hadamardMatrix i j • v j

/-- A bilinear map turns the Hadamard orthogonality identity into the
four-channel cancellation used by the Regge coproduct proof. -/
theorem hadamard_bilinear_cancellation
    (B : M →ₗ[ℚ] N →ₗ[ℚ] P) (y : Four → M) (b : Four → N) :
    ∑ i, B (hadamardTransform y i) (hadamardTransform b i) =
      (4 : ℚ) • ∑ j, B (y j) (b j) := by
  classical
  simp [hadamardTransform, hadamardMatrix, Fin.sum_univ_succ,
    map_add, map_neg]
  module

/-- The normalized transform `R = H / 2` acting on a four-tuple. -/
def reggeTransform (v : Four → M) : Four → M :=
  fun i => ∑ j, reggeMatrix i j • v j

/-- Normalized form of the cancellation: applying the actual Regge matrix
to both variables preserves the sum of the four bilinear channels. -/
theorem regge_bilinear_cancellation
    (B : M →ₗ[ℚ] N →ₗ[ℚ] P) (y : Four → M) (b : Four → N) :
    ∑ i, B (reggeTransform y i) (reggeTransform b i) =
      ∑ j, B (y j) (b j) := by
  classical
  simp [reggeTransform, reggeMatrix, Fin.sum_univ_succ, map_add]
  module

end Bilinear

section Tensor

variable {M N : Type*}
  [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]

/-- Tensor-product form of the four-channel identity. -/
theorem hadamard_tensor_cancellation (y : Four → M) (b : Four → N) :
    ∑ i, hadamardTransform y i ⊗ₜ[ℚ] hadamardTransform b i =
      (4 : ℚ) • ∑ j, y j ⊗ₜ[ℚ] b j := by
  exact hadamard_bilinear_cancellation (TensorProduct.mk ℚ M N) y b

/-- Exact tensor identity for the normalized Regge action. -/
theorem regge_tensor_cancellation (y : Four → M) (b : Four → N) :
    ∑ i, reggeTransform y i ⊗ₜ[ℚ] reggeTransform b i =
      ∑ j, y j ⊗ₜ[ℚ] b j := by
  exact regge_bilinear_cancellation (TensorProduct.mk ℚ M N) y b

/-- An unchanged fixed channel contributes no defect. -/
theorem fixed_channel_cancellation (l : M) (a : N) :
    l ⊗ₜ[ℚ] a - l ⊗ₜ[ℚ] a = 0 := sub_self _

/-- Four moving channels plus the two pointwise-fixed opposite channels:
this is the exact six-term algebraic identity used in the coproduct proof. -/
theorem six_channel_tensor_invariance
    (y : Four → M) (b : Four → N)
    (fixedLength₀ fixedLength₁ : M) (fixedAngle₀ fixedAngle₁ : N) :
    fixedLength₀ ⊗ₜ[ℚ] fixedAngle₀ + fixedLength₁ ⊗ₜ[ℚ] fixedAngle₁ +
        ∑ i, reggeTransform y i ⊗ₜ[ℚ] reggeTransform b i =
      fixedLength₀ ⊗ₜ[ℚ] fixedAngle₀ + fixedLength₁ ⊗ₜ[ℚ] fixedAngle₁ +
        ∑ j, y j ⊗ₜ[ℚ] b j := by
  rw [regge_tensor_cancellation]

end Tensor

end SphericalReggeScissors
