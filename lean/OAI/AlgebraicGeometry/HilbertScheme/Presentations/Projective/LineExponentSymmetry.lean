import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineRationalCocycle

/-! # Line Exponent Symmetry -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineExponentSymmetry

noncomputable section

/-! Reversing a standard overlap reverses its coordinate ratio and
its transition function, leaving the canonical exponent unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v

theorem rational_transition_inverse_exponents {K : Type u} [Field K] {σ : Type v}
    (i j : σ) (hij : i ≠ j) (c d : Kˣ) (a b : ℤ)
    (h : RationalTransitionExponentComparison.rationalProjectiveMonomial c i j a * RationalTransitionExponentComparison.rationalProjectiveMonomial d j i b = 1) : a = b := by
  classical
  have he := congrArg (RationalCoordinateDegrees.rationalCoordinateDegree i) h
  rw [RationalCoordinateDegrees.rationalCoordinateDegree_mul i _ _ (RationalTransitionExponentComparison.rationalProjectiveMonomial_ne_zero c i j a)
    (RationalTransitionExponentComparison.rationalProjectiveMonomial_ne_zero d j i b), RationalTransitionExponentComparison.rationalProjectiveMonomial_degree,
    RationalTransitionExponentComparison.rationalProjectiveMonomial_degree] at he
  have h1 : RationalCoordinateDegrees.rationalCoordinateDegree (K := K) i 1 = 0 := by
    unfold RationalCoordinateDegrees.rationalCoordinateDegree
    rw [map_one, WithZero.log_one]
  rw [h1] at he
  simp [hij] at he
  omega

variable (K : Type u) [Field K] {n : ℕ}
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)))

theorem projectiveLineTransitionValue_field_self (i : Fin (n + 1)) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i i (LineTransitionPowers.projectiveLineTransitionValue K L i i) = 1 := by
  rw [LineRationalCocycle.projectiveLineTransitionValue_field, FrameTransitionCocycles.frameTransitionValue_self, map_one]

theorem projectiveLineTransitionExponent_symm (i j : Fin (n + 1)) (hji : j ≠ i) :
    FrameExponents.projectiveLineTransitionExponent K i j hji L = FrameExponents.projectiveLineTransitionExponent K j i hji.symm L := by
  obtain ⟨c, hc⟩ := OverlapRationalMonomials.projectiveOverlapFunctionFieldMap_unit K i j hji (LineTransitionPowers.projectiveLineTransitionUnit K L i j)
  obtain ⟨d, hd⟩ := OverlapRationalMonomials.projectiveOverlapFunctionFieldMap_unit K j i hji.symm (LineTransitionPowers.projectiveLineTransitionUnit K L j i)
  have h := LineRationalCocycle.projectiveLineTransitionValue_rational_cocycle K L i j i
  rw [projectiveLineTransitionValue_field_self] at h
  have hc' : OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (LineTransitionPowers.projectiveLineTransitionValue K L i j) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial c i j (FrameExponents.projectiveLineTransitionExponent K i j hji L) := by
    simpa only [FrameExponents.projectiveLineTransitionExponent, LineTransitionPowers.projectiveLineTransitionUnit, IsUnit.unit_spec] using hc
  have hd' : OverlapFunctionField.projectiveOverlapFunctionFieldMap K j i (LineTransitionPowers.projectiveLineTransitionValue K L j i) =
      RationalTransitionExponentComparison.rationalProjectiveMonomial d j i (FrameExponents.projectiveLineTransitionExponent K j i hji.symm L) := by
    simpa only [FrameExponents.projectiveLineTransitionExponent, LineTransitionPowers.projectiveLineTransitionUnit, IsUnit.unit_spec] using hd
  rw [hc', hd'] at h
  exact rational_transition_inverse_exponents i j hji.symm c d _ _ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineExponentSymmetry
