import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertPolynomial
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertPolynomialDegreeBound
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BoundedEventualPolynomial

/-! # Integer Hilbert Degree Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertDegreeBound

noncomputable section

/-! Integer shifts preserve the ambient degree bound for homogeneous Hilbert polynomials. -/

open _root_.MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem integerIdealDegree_eventuallyPolynomialOfDegree {K : Type u} [Field K] {r : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 1)) K))
    (hI : I.IsHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K)) (e : ℤ) :
    BoundedEventualPolynomial.EventuallyPolynomialOfDegree (fun n =>
      (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) I ((n : ℤ) - e)) : ℚ)) r := by
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin (r + 1)) K) :=
    ⟨I, IntegerHilbertPolynomial.ideal_nat_homogeneous_of_integer I hI⟩
  obtain ⟨P, ⟨b, hb⟩, hP⟩ := HilbertPolynomialDegreeBound.exists_hilbertPolynomial_natDegree_le J
  have hshift : (P.comp (Polynomial.X - Polynomial.C (e : ℚ))).natDegree ≤ r := by
    exact (Polynomial.natDegree_comp_le.trans (by
      rw [Polynomial.natDegree_X_sub_C, mul_one])).trans hP
  refine ⟨P.comp (Polynomial.X - Polynomial.C (e : ℚ)), hshift, b + e.toNat, fun n hn => ?_⟩
  let k : ℕ := ((n : ℤ) - e).toNat
  have hk : (k : ℤ) = (n : ℤ) - e := by dsimp only [k]; omega
  have hbk : b ≤ k := by dsimp only [k]; omega
  change (Module.finrank K
    (GradedCyclicDegreeSequence.DegreeQuotient (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) I ((n : ℤ) - e)) : ℚ) = _
  rw [← hk]
  have hp := hb k hbk
  change (Module.finrank K
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I k) : ℚ) = P.eval (k : ℚ) at hp
  have heq : (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) I (k : ℤ)) : ℚ) =
      P.eval (k : ℚ) := by
    unfold GradedCyclicDegreeSequence.DegreeQuotient GradedCyclicDegreeSequence.degreeRelations
    rw [HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
    exact hp
  rw [heq, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  exact_mod_cast hk

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertDegreeBound
