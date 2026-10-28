import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Characters.CM

noncomputable section

/-! Lift the actual complex Hecke eigenvalues to algebraic characters.
Their rational characteristic polynomials prove algebraicity. The lift
preserves the eigenvalues in the fixed complex embedding. -/

open scoped TensorProduct
open _root_.Module.End
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM

variable {U J : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]

theorem eigenvalues_algebraic (T : J → Module.End ℚ U) (χ : J → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun j => (T j).baseChange ℂ) χ ≠ ⊥) (j : J) :
    IsAlgebraic ℚ (χ j) := by
  have hn : Module.End.HasUnifEigenvalue ((T j).baseChange ℂ) (χ j) ⊤ := by
    intro hz
    exact hχ (eq_bot_iff.mpr ((iInf_le _ j).trans hz.le))
  have he : Module.End.HasEigenvalue ((T j).baseChange ℂ) (χ j) := hn.lt zero_lt_one
  have hp := (hasEigenvalue_iff_isRoot_charpoly _ _).mp he
  rw [LinearMap.charpoly_baseChange] at hp
  apply IsIntegral.isAlgebraic
  refine ⟨(T j).charpoly, LinearMap.charpoly_monic _, ?_⟩
  simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hp

variable {H : Type*} [CommRing H] [Algebra ℚ H]

def complexAction (T : H →ₐ[ℚ] Module.End ℚ U) :
    H →+* Module.End ℂ (ℂ ⊗[ℚ] U) where
  toFun h := (T h).baseChange ℂ
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, LinearMap.baseChange_mul]
  map_zero' := by simp
  map_add' a b := by simp only [map_add, LinearMap.baseChange_add]

def algebraicCharacter (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) :
    H →ₐ[ℚ] Coefficients.CM.algebraicField :=
  (HeckeCharacters.CM.jointCharacter (complexAction T) χ hχ).codRestrict Coefficients.CM.algebraicField.toSubalgebra
    (fun h => mem_algebraicClosure_iff.mpr (eigenvalues_algebraic T χ hχ h))

theorem algebraicCharacter_apply (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) (h : H) :
    (algebraicCharacter T χ hχ h : ℂ) = χ h := rfl

/-- Identify the abstract algebraic closure used by GeometricComparison with the actual
algebraic numbers in ℂ. This choice is made once, before taking conjugates. -/
def closureEquiv : AlgebraicClosure ℚ ≃ₐ[ℚ] Coefficients.CM.algebraicField := by
  let : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  let : IsAlgClosure ℚ Coefficients.CM.algebraicField := algebraicClosure.isAlgClosure ℚ ℂ
  exact IsAlgClosure.equiv ℚ (AlgebraicClosure ℚ) Coefficients.CM.algebraicField

def complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ :=
  Coefficients.CM.algebraicField.val.comp closureEquiv.toAlgHom

def closureCharacter (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) :
    H →ₐ[ℚ] AlgebraicClosure ℚ :=
  closureEquiv.symm.toAlgHom.comp (algebraicCharacter T χ hχ)

theorem closureCharacter_apply (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) (h : H) :
    complexEmbedding (closureCharacter T χ hχ h) = χ h := by
  change (closureEquiv (closureEquiv.symm (algebraicCharacter T χ hχ h)) : ℂ) = χ h
  rw [closureEquiv.apply_symm_apply, algebraicCharacter_apply]

theorem closureCharacter_jointSpace (T : H →ₐ[ℚ] Module.End ℚ U) (χ : H → ℂ)
    (hχ : HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ ≠ ⊥) :
    HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ)
      (fun h => complexEmbedding (closureCharacter T χ hχ h)) =
      HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) χ := by
  simp only [closureCharacter_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Characters.CM
