import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicDegreeSequence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Integer Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertPolynomial

noncomputable section

/-! Hilbert polynomials for integer shifts of homogeneous coordinate quotients. -/

open _root_.MvPolynomial
universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ideal_nat_homogeneous_of_integer {σ : Type u} [Fintype σ]
    {R : Type v} [CommRing R] (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R)) :
    I.IsHomogeneous (homogeneousSubmodule σ R) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) I).mp hI
  rw [hS]
  apply Ideal.homogeneous_span
  rintro p ⟨x, _, rfl⟩
  obtain ⟨d, hd⟩ := x.property
  by_cases h : 0 ≤ d
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact ⟨n, (HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat (σ := σ) R n) ▸ hd⟩
  · have hz : x.val = 0 := by
      rw [GradedPieceFiniteness.polynomialIntegerGrading_eq_bot_of_neg R d (by omega)] at hd
      exact hd
    exact ⟨0, hz ▸ (homogeneousSubmodule σ R 0).zero_mem⟩

theorem integerIdealDegree_eventuallyPolynomial {K : Type u} [Field K] {r : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 1)) K))
    (hI : I.IsHomogeneous (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K)) (e : ℤ) :
    EventualPolynomial.EventuallyPolynomial (fun n =>
      (Module.finrank K (GradedCyclicDegreeSequence.DegreeQuotient (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading K) I ((n : ℤ) - e)) : ℚ)) := by
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin (r + 1)) K) :=
    ⟨I, ideal_nat_homogeneous_of_integer I hI⟩
  obtain ⟨P, b, hb⟩ := HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial J
  refine ⟨P.comp (Polynomial.X - Polynomial.C (e : ℚ)), b + e.toNat, fun n hn => ?_⟩
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

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerHilbertPolynomial
