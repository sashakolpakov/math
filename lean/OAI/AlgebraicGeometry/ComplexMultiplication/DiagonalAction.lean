import OAI.AlgebraicGeometry.ComplexMultiplication.Definitions
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv

/-! # Diagonal Action -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.DiagonalAction

noncomputable section

/-! # The original diagonal action as a faithful algebra representation -/

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {ι : Type*}
  (K : ι → Type) [∀ i, Field (K i)] [∀ i, Algebra ℚ (K i)]
  (e : V ≃ₗ[ℚ] ((i : ι) → K i))

/-- The original transported regular action, bundled as a rational algebra homomorphism. -/
def diagonalActionAlgHom : ((i : ι) → K i) →ₐ[ℚ] Module.End ℚ V :=
  (e.symm.conjAlgEquiv ℚ).toAlgHom.comp (Algebra.lmul ℚ ((i : ι) → K i))

/-- Bundling changes neither the original action nor the module on which it acts. -/
theorem diagonalActionAlgHom_apply (a : (i : ι) → K i) :
    diagonalActionAlgHom K e a = Definitions.diagonalAction K e a := rfl

/-- The rank-one regular representation of the entire field product is faithful. -/
theorem diagonalActionAlgHom_injective : Function.Injective (diagonalActionAlgHom K e) :=
  (e.symm.conjAlgEquiv ℚ).injective.comp (Algebra.lmul_injective)

/-- The supplied model intertwines the actual transported action with multiplication. -/
theorem model_diagonalAction (a : (i : ι) → K i) (v : V) :
    e (diagonalActionAlgHom K e a v) = a * e v := by
  simp [diagonalActionAlgHom, LinearEquiv.conjAlgEquiv_apply, Algebra.coe_lmul_eq_mul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.DiagonalAction
