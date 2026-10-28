import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Definitions

noncomputable section

/-! Definitions used in the ReferenceFamily statement. -/

variable {E : Type}
  [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [IsGalois ℚ E]

/-- Principal special-unitary level on the specified lattice. -/
def SpecialUnitaryPrincipalLevel
    (b : E) (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : Prop :=
  NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel b Λ N g ∧
    LinearMap.det g.toLinearMap = 1

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Definitions
