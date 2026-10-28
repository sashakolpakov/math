import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Hom

/-! # Subquotient Character Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubquotientCharacterRank.Construction

noncomputable section

/-! Additive characters of a quotient of an integral sublattice have
dimension bounded by the ambient lattice rank. This is the algebraic
bound for tangent characters of finite diagonalizable subquotients. -/

variable {k Q : Type*} [Field k] [AddCommGroup Q] {d : ℕ}
  (S : Submodule ℤ (Fin d → ℤ)) (p : S →+ Q)

def subquotientCharacterCoordinates : (Q →+ k) →ₗ[k] (Fin (Module.finrank ℤ S) → k) where
  toFun χ i := χ (p (Module.finBasis ℤ S i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subquotientCharacterCoordinates_injective (hp : Function.Surjective p) :
    Function.Injective (subquotientCharacterCoordinates (k := k) S p) := by
  intro χ ψ h
  have he : (χ.comp p).toIntLinearMap = (ψ.comp p).toIntLinearMap := by
    apply (Module.finBasis ℤ S).ext
    intro i
    exact congrFun h i
  apply AddMonoidHom.ext
  intro x
  obtain ⟨s, rfl⟩ := hp x
  exact LinearMap.congr_fun he s

theorem subquotientCharacter_finrank_le (hp : Function.Surjective p) :
    Module.finrank k (Q →+ k) ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (subquotientCharacterCoordinates_injective (k := k) S p hp)
  have hS := S.finrank_le
  calc
    Module.finrank k (Q →+ k) ≤ Module.finrank ℤ S := by simpa using h
    _ ≤ d := by simpa using hS

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SubquotientCharacterRank.Construction
