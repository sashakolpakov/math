import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentDegree

/-! # Fraction Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FractionDegrees.ProjectiveCech

noncomputable section

/-! Comparison of homogeneous polynomial fractions with the Laurent basis degree. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.ModuleRestriction.GradedModules

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

theorem sum_inversionExponent (s : Finset σ) :
    (∑ i, (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ)) = (s.card : ℤ) := by
  simp [LaurentExponents.ProjectiveCech.inversionExponent_apply]

theorem exponentDegree_ofNumerator (s : Finset σ) (m : σ →₀ ℕ) (k : ℕ) :
    LaurentDegree.ProjectiveCech.exponentDegree (LaurentExponents.ProjectiveCech.exponentOfNumerator s m k).val =
      Finsupp.weight (fun _ : σ => (1 : ℤ)) m - (k : ℤ) * (s.card : ℤ) := by
  change (∑ i, ((m i : ℤ) - (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ))) = _
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_inversionExponent, Finsupp.weight_eq_sum]
  simp only [nsmul_eq_mul, mul_one]

theorem exponentOfNumerator_numeratorExponent {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s)
    (k : ℕ) (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) :
    LaurentExponents.ProjectiveCech.exponentOfNumerator s (LaurentExponents.ProjectiveCech.numeratorExponent a k) k = a := by
  apply Subtype.ext
  funext i
  change (LaurentExponents.ProjectiveCech.numeratorExponent a k i : ℤ) - (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ) = a.val i
  rw [LaurentExponents.ProjectiveCech.numeratorExponent_cast a k hk, add_sub_cancel_right]

theorem numeratorExponent_weight {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s)
    (k : ℕ) (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) (LaurentExponents.ProjectiveCech.numeratorExponent a k) =
      LaurentDegree.ProjectiveCech.exponentDegree a.val + (k : ℤ) * (s.card : ℤ) := by
  have h := exponentDegree_ofNumerator s (LaurentExponents.ProjectiveCech.numeratorExponent a k) k
  rw [exponentOfNumerator_numeratorExponent a k hk] at h
  omega

theorem chartFractionLinearMap_homogeneous (s : Finset σ) (d : ℤ) (k : ℕ)
    (p : MvPolynomial σ R) (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (d + (k : ℤ) * (s.card : ℤ))) :
    LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k p ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s d := by
  apply MvPolynomial.IsWeightedHomogeneous.induction_on
    (motive := fun p _ => LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k p ∈ LaurentDegree.ProjectiveCech.laurentDegreeSubmodule R s d)
    ?_ ?_ ?_ hp
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro p q _ _ hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro m r hm
    have hr : monomial m r = r • monomial m (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hr, map_smul, LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply, ← LaurentMonomials.ProjectiveCech.laurentMonomial_ofNumerator]
    apply Submodule.smul_mem
    have hd : LaurentDegree.ProjectiveCech.exponentDegree (LaurentExponents.ProjectiveCech.exponentOfNumerator s m k).val = d := by
      rw [exponentDegree_ofNumerator, hm, add_sub_cancel_right]
    exact hd ▸ LaurentDegree.ProjectiveCech.laurentMonomial_mem_degree R s (LaurentExponents.ProjectiveCech.exponentOfNumerator s m k)

theorem laurentMonomial_homogeneous_fraction (s : Finset σ) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    ∃ (k : ℕ) (p : MvPolynomial σ R),
      p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (LaurentDegree.ProjectiveCech.exponentDegree a.val + (k : ℤ) * (s.card : ℤ)) ∧
      LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k p = LaurentMonomials.ProjectiveCech.laurentMonomial R a := by
  refine ⟨LaurentExponents.ProjectiveCech.denominatorBound a, monomial (LaurentExponents.ProjectiveCech.numeratorExponent a (LaurentExponents.ProjectiveCech.denominatorBound a)) 1, ?_, ?_⟩
  · exact isWeightedHomogeneous_monomial _ _ _ (numeratorExponent_weight a _ le_rfl)
  · rw [LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FractionDegrees.ProjectiveCech
