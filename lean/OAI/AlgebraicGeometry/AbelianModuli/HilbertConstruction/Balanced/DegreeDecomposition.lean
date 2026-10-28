import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.MonomialSpan
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra
import Mathlib.Algebra.DirectSum.Module

/-! # Degree Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DegreeDecomposition

noncomputable section

/-! Balanced monomial degree pieces span the algebra. For actual
determinants these pieces are independent, as witnessed by polynomial
homogeneity in any one marked-point block. -/
open scoped BigOperators Classical
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {κ : Type u} [Fintype κ] {ι : Type v}
variable {R A : Type w} [CommRing R] [CommRing A] [Algebra R A]

theorem balancedMonomialDegreeSpan_iSup (D : κ → A) (w : κ → ι → ℕ) (i : ι) :
    (⨆ n, MonomialSpan.balancedMonomialDegreeSpan D w i n) = (MonomialAlgebra.balancedMonomialAlgebra R D w).toSubmodule := by
  apply le_antisymm
  · exact iSup_le (MonomialSpan.balancedMonomialDegreeSpan_le D w i)
  · rw [MonomialSpan.balancedMonomialAlgebra_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact (le_iSup (fun n => MonomialSpan.balancedMonomialDegreeSpan (R := R) D w i n)
      (ExponentFiniteGeneration.monomialMultiDegree w a i)) (Submodule.subset_span ⟨a, ⟨ha, rfl⟩, rfl⟩)

variable {r m : ℕ}

theorem balancedDeterminantDegreeSpan_le_weighted (i : Fin m) (n : ℕ) :
    MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial (r := r) R)
      DeterminantBlockDegrees.labeledDeterminantWeight i n ≤ MvPolynomial.weightedHomogeneousSubmodule R (DeterminantBlockDegrees.pointBlockWeight i) n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  change (MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) a).IsWeightedHomogeneous (DeterminantBlockDegrees.pointBlockWeight i) n
  rw [← ha.2]
  exact DeterminantBlockDegrees.exponentMonomial_blockHomogeneous _ _ DeterminantBlockDegrees.labeledDeterminantPolynomial_blockHomogeneous a i

theorem balancedDeterminantDegreeSpan_independent (i : Fin m) :
    iSupIndep (fun n => MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      (DeterminantBlockDegrees.labeledDeterminantWeight (r := r)) i n) := by
  let := MvPolynomial.weightedDecomposition R (DeterminantBlockDegrees.pointBlockWeight (r := r) i)
  have h := (DirectSum.Decomposition.isInternal
    (MvPolynomial.weightedHomogeneousSubmodule R (DeterminantBlockDegrees.pointBlockWeight (r := r) i))).submodule_iSupIndep
  exact h.mono (balancedDeterminantDegreeSpan_le_weighted i)

theorem balancedDeterminantDegreeSpan_zero (hr : 0 < r) (i : Fin m) :
    MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      (DeterminantBlockDegrees.labeledDeterminantWeight (r := r)) i 0 = Submodule.span R {(1 : MvPolynomial (Fin m × Fin r) R)} := by
  unfold MonomialSpan.balancedMonomialDegreeSpan
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hz := (DeterminantAlgebra.balancedDeterminantMonomial_degree_zero_iff hr a ha.1 i).mp ha.2
    rw [hz, MonomialAlgebra.exponentMonomial_zero]
    exact Set.mem_singleton _
  · rintro rfl
    refine ⟨0, ⟨(ExponentFiniteGeneration.balancedExponentMonoid _).zero_mem, ?_⟩, MonomialAlgebra.exponentMonomial_zero _⟩
    simp only [ExponentFiniteGeneration.monomialMultiDegree, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DegreeDecomposition
