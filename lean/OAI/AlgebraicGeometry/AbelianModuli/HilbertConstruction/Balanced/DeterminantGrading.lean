import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DegreeDecomposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInternalDecomposition
import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Determinant Grading -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantGrading

noncomputable section

/-! The finite-type balanced determinant algebra carries its actual
grading by common marked-point degree. -/
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (r m : ℕ)

def balancedDeterminantGrading (i : Fin m) (n : ℕ) :
    Submodule R (DeterminantAlgebra.balancedDeterminantAlgebra R r m) :=
  (MonomialSpan.balancedMonomialDegreeSpan (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
    DeterminantBlockDegrees.labeledDeterminantWeight i n).comap (DeterminantAlgebra.balancedDeterminantAlgebra R r m).toSubmodule.subtype

instance balancedDeterminantGradedAlgebra (i : Fin m) :
    GradedAlgebra (balancedDeterminantGrading R r m i) where
  toDecomposition := by
    have h : DirectSum.IsInternal (balancedDeterminantGrading R r m i) := by
      convert (SubalgebraInternalDecomposition.subalgebra_internalDecomposition (DeterminantAlgebra.balancedDeterminantAlgebra R r m)
    (fun n => MonomialSpan.balancedMonomialDegreeSpan (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i n)
    (MonomialSpan.balancedMonomialDegreeSpan_le _ _ i)
    (DegreeDecomposition.balancedDeterminantDegreeSpan_independent i)
    (DegreeDecomposition.balancedMonomialDegreeSpan_iSup _ _ i)) using 1; rfl
    exact h.chooseDecomposition
  toGradedMonoid := {
    one_mem := by
      change (1 : MvPolynomial (Fin m × Fin r) R) ∈
        MonomialSpan.balancedMonomialDegreeSpan _ _ i 0
      apply Submodule.subset_span
      refine ⟨0, ⟨(ExponentFiniteGeneration.balancedExponentMonoid _).zero_mem, ?_⟩, MonomialAlgebra.exponentMonomial_zero _⟩
      simp only [ExponentFiniteGeneration.monomialMultiDegree, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    mul_mem := by
      intro n t x y hx hy
      exact MonomialSpan.balancedMonomialDegreeSpan_mul _ _ i n t (Submodule.mul_mem_mul hx hy) }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantGrading
