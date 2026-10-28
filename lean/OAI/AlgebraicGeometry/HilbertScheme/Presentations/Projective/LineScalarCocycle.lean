import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineCommonExponent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalCoordinateMonomials

/-! # Line Scalar Cocycle -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineScalarCocycle

noncomputable section

/-! The remaining scalar factors of projective line-bundle transitions
form a field-unit cocycle, explicitly determined by one row of scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

theorem projectiveLineTransitionValue_common_monomial_all (i j : Fin (n + 1)) :
    ∃ c : Kˣ, OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial c i j (LineCommonExponent.projectiveLineCommonExponent K L) := by
  by_cases hji : j = i
  · subst j
    exact ⟨1, (LineExponentSymmetry.projectiveLineTransitionValue_field_self K L i).trans (RationalCoordinateMonomials.rationalProjectiveMonomial_one_self _ _).symm⟩
  · exact LineCommonExponent.projectiveLineTransitionValue_common_monomial K L i j hji

def projectiveLineTransitionScalar (i j : Fin (n + 1)) : Kˣ :=
  (projectiveLineTransitionValue_common_monomial_all K L i j).choose

theorem projectiveLineTransitionScalar_spec (i j : Fin (n + 1)) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial (projectiveLineTransitionScalar K L i j) i j (LineCommonExponent.projectiveLineCommonExponent K L) :=
  (projectiveLineTransitionValue_common_monomial_all K L i j).choose_spec

theorem projectiveLineTransitionScalar_cocycle (i j k : Fin (n + 1)) :
    projectiveLineTransitionScalar K L i j * projectiveLineTransitionScalar K L j k =
      projectiveLineTransitionScalar K L i k := by
  apply RationalCoordinateMonomials.rationalProjectiveMonomial_scalar_injective i k (LineCommonExponent.projectiveLineCommonExponent K L)
  dsimp only
  rw [← RationalCoordinateMonomials.rationalProjectiveMonomial_cocycle, ← projectiveLineTransitionScalar_spec,
    ← projectiveLineTransitionScalar_spec, ← projectiveLineTransitionScalar_spec]
  exact LineRationalCocycle.projectiveLineTransitionValue_rational_cocycle K L i j k

theorem projectiveLineTransitionScalar_self (i : Fin (n + 1)) :
    projectiveLineTransitionScalar K L i i = 1 := by
  apply RationalCoordinateMonomials.rationalProjectiveMonomial_scalar_injective i i (LineCommonExponent.projectiveLineCommonExponent K L)
  dsimp only
  rw [← projectiveLineTransitionScalar_spec, LineExponentSymmetry.projectiveLineTransitionValue_field_self,
    RationalCoordinateMonomials.rationalProjectiveMonomial_one_self]

theorem projectiveLineTransitionScalar_from_base (i j : Fin (n + 1)) :
    projectiveLineTransitionScalar K L i j =
      (projectiveLineTransitionScalar K L 0 i)⁻¹ * projectiveLineTransitionScalar K L 0 j := by
  rw [← projectiveLineTransitionScalar_cocycle K L 0 i j, inv_mul_cancel_left]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineScalarCocycle
