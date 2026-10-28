import Mathlib

/-! # Characters -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Characters.Construction

noncomputable section

/-! Allowed splitting characters for a quadratic local field extension.
These conditions concern characters only and contain no lift assumption. -/

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]

def IsExtensionQuadraticCharacter (ω : Fˣ →ₜ* Circle) : Prop :=
  ∀ a : Fˣ, ω a = 1 ↔ ∃ b : Eˣ, Algebra.norm F (b : E) = (a : F)

def HasSplittingRestriction (ω : Fˣ →ₜ* Circle) (d : ℕ)
    (χ : Eˣ →ₜ* Circle) : Prop :=
  ∀ a : Fˣ, χ (Units.map (algebraMap F E).toMonoidHom a) = ω a ^ d

structure SplittingCharacters (F E : Type) [NormedField F] [NormedField E]
    [Algebra F E] (m n : ℕ) where
  quadratic : Fˣ →ₜ* Circle
  quadratic_kernel : IsExtensionQuadraticCharacter (E := E) quadratic
  hermitian : Eˣ →ₜ* Circle
  skewHermitian : Eˣ →ₜ* Circle
  hermitian_restriction : HasSplittingRestriction quadratic m hermitian
  skewHermitian_restriction : HasSplittingRestriction quadratic n skewHermitian

theorem quadraticCharacter_square [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (ω : Fˣ →ₜ* Circle)
    (hω : IsExtensionQuadraticCharacter (E := E) ω) (a : Fˣ) : ω a ^ 2 = 1 := by
  rw [← map_pow]
  apply (hω (a ^ 2)).mpr
  refine ⟨Units.map (algebraMap F E).toMonoidHom a, ?_⟩
  change Algebra.norm F (algebraMap F E (a : F)) = (a : F) ^ 2
  rw [Algebra.norm_algebraMap, hQuadratic]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Characters.Construction
