import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseBalancedFrameCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantGrading

/-! # Frame Coordinate Polynomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameCoordinatePolynomials

noncomputable section

/-! Completing the coordinate exponents gives actual elements of the
balanced determinant algebra, all in the denominator's graded piece. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}

def balancedDeterminantMonomialElement (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) : DeterminantAlgebra.balancedDeterminantAlgebra R r m :=
  ⟨MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a, Algebra.subset_adjoin ⟨a, ha, rfl⟩⟩

theorem balancedDeterminantMonomialElement_mem_grading (a : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i : Fin m) :
    balancedDeterminantMonomialElement R a ha ∈
      DeterminantGrading.balancedDeterminantGrading R r m i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) := by
  apply Submodule.subset_span
  exact ⟨a, ⟨ha, rfl⟩, rfl⟩

theorem frameCompletion_coordinate_degree (σ : Fin r → Fin m) (e z : Fin m) (c k : Fin r)
    (a C : (Fin r → Fin m) → ℕ) (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) (i : Fin m) :
    ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (C + Frame.CoordinateExponents.frameCoordinateExponent σ e z k) i =
      ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i := by
  rw [ExponentFiniteGeneration.monomialMultiDegree_add, Frame.CoordinateExponents.frameCoordinateExponent_degrees_equal σ e z k c,
    ← ExponentFiniteGeneration.monomialMultiDegree_add, hC]

def balancedFrameCoordinateNumerator (σ : Fin r → Fin m) (e z : Fin m) (c k : Fin r)
    (a C : (Fin r → Fin m) → ℕ) (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) : DeterminantAlgebra.balancedDeterminantAlgebra R r m :=
  balancedDeterminantMonomialElement R (C + Frame.CoordinateExponents.frameCoordinateExponent σ e z k)
    (ExponentCompletion.balanced_completion_of_same_degree DeterminantBlockDegrees.labeledDeterminantWeight a
      (Frame.CoordinateExponents.frameCoordinateExponent σ e z c) C (Frame.CoordinateExponents.frameCoordinateExponent σ e z k) ha hC
      (Frame.CoordinateExponents.frameCoordinateExponent_degrees_equal σ e z k c))

theorem balancedFrameCoordinateNumerator_mem_grading (σ : Fin r → Fin m)
    (e z : Fin m) (c k : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) (i : Fin m) :
    balancedFrameCoordinateNumerator R σ e z c k a C ha hC ∈
      DeterminantGrading.balancedDeterminantGrading R r m i (ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i) := by
  unfold balancedFrameCoordinateNumerator
  rw [← frameCompletion_coordinate_degree σ e z c k a C hC i]
  exact balancedDeterminantMonomialElement_mem_grading R _ _ i

theorem balancedFrameCoordinateNumerator_selected (σ : Fin r → Fin m)
    (e z : Fin m) (c : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) :
    balancedFrameCoordinateNumerator R σ e z c c a C ha hC =
      balancedDeterminantMonomialElement R a ha := by
  apply Subtype.ext
  change MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c) = _
  rw [hC]
  rfl

theorem balancedFrameCoordinateNumerator_crossMultiply (σ : Fin r → Fin m)
    (e z : Fin m) (c k : Fin r) (a C : (Fin r → Fin m) → ℕ)
    (ha : a ∈ ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : C + Frame.CoordinateExponents.frameCoordinateExponent σ e z c = a) :
    (balancedFrameCoordinateNumerator R σ e z c k a C ha hC).val *
        MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (Frame.CoordinateExponents.frameCoordinateExponent σ e z c) =
      (balancedDeterminantMonomialElement R a ha).val *
        MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (Frame.CoordinateExponents.frameCoordinateExponent σ e z k) := by
  change MonomialAlgebra.exponentMonomial _ (C + Frame.CoordinateExponents.frameCoordinateExponent σ e z k) * _ =
    MonomialAlgebra.exponentMonomial _ a * _
  rw [← hC, MonomialAlgebra.exponentMonomial_add, MonomialAlgebra.exponentMonomial_add]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FrameCoordinatePolynomials
