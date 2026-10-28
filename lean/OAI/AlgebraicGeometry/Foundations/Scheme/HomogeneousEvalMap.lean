import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous Eval Map -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap

section

/-!
# Evaluation of homogeneous polynomials under changes of representative

The results in this file concern the actual `MvPolynomial.IsHomogeneous`
predicate and polynomial evaluation. They include degree zero and do not
require a finite type of variables: each individual monomial has finite support.
-/

open scoped BigOperators

variable {K σ : Type*}

/-- Evaluating a homogeneous polynomial on a scaled coordinate vector multiplies
its value by the corresponding power of the scalar. -/
theorem eval_smul_of_isHomogeneous [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (c : K) (v : σ → K) :
    MvPolynomial.eval (c • v) f = c ^ d * MvPolynomial.eval v f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : m.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hf (MvPolynomial.mem_support_iff.mp hm)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_apply, hm']
  ac_rfl

/-- A homogeneous polynomial of positive degree vanishes at the zero vector. -/
theorem eval_zero_of_isHomogeneous [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hd : d ≠ 0) : MvPolynomial.eval (0 : σ → K) f = 0 := by
  simpa only [zero_smul, zero_pow hd, zero_mul] using
    eval_smul_of_isHomogeneous hf (0 : K) (0 : σ → K)

/-- A homogeneous polynomial of degree zero is exactly its constant term. -/
theorem eq_C_of_isHomogeneous_zero [CommSemiring K]
    {f : MvPolynomial σ K} (hf : f.IsHomogeneous 0) :
    f = MvPolynomial.C (f.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr hf

/-- Degree-zero homogeneous equations evaluate to their constant coefficient
at every coordinate vector, including the zero vector. -/
theorem eval_of_isHomogeneous_zero [CommSemiring K]
    {f : MvPolynomial σ K} (hf : f.IsHomogeneous 0) (v : σ → K) :
    MvPolynomial.eval v f = f.coeff 0 := by
  conv_lhs => rw [eq_C_of_isHomogeneous_zero hf]
  exact MvPolynomial.eval_C (f.coeff 0)

/-- The zero condition of a homogeneous polynomial is unchanged by multiplying
all coordinates by a nonzero scalar. No positivity hypothesis on its degree is
needed. -/
theorem eval_smul_eq_zero_iff [Field K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    {c : K} (hc : c ≠ 0) (v : σ → K) :
    MvPolynomial.eval (c • v) f = 0 ↔ MvPolynomial.eval v f = 0 := by
  rw [eval_smul_of_isHomogeneous hf c v]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d hc))

/-- A family of homogeneous equations, whose degrees may vary with the
equation, has a common zero condition invariant under nonzero scaling. -/
theorem forall_eval_smul_eq_zero_iff [Field K]
    {ι : Type*} (f : ι → MvPolynomial σ K) (d : ι → ℕ)
    (hf : ∀ i, (f i).IsHomogeneous (d i)) {c : K} (hc : c ≠ 0)
    (v : σ → K) :
    (∀ i, MvPolynomial.eval (c • v) (f i) = 0) ↔
      ∀ i, MvPolynomial.eval v (f i) = 0 := by
  exact forall_congr' fun i => eval_smul_eq_zero_iff (hf i) hc v

end

/-!
# Homogeneous evaluation after a coefficient homomorphism

The scalar may lie in the target ring of evaluation, as needed for homogeneous
localizations and projective affine charts.
-/

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]

/-- Homogeneous evaluation scales by the degree even after mapping the
coefficients into a different commutative semiring. -/
theorem eval₂_smul_of_isHomogeneous {f : MvPolynomial ι R} {d : ℕ}
    (hf : f.IsHomogeneous d) (φ : R →+* S) (c : S) (v : ι → S) :
    MvPolynomial.eval₂ φ (c • v) f = c ^ d * MvPolynomial.eval₂ φ v f := by
  simpa only [MvPolynomial.eval_map] using
    eval_smul_of_isHomogeneous (hf.map φ) c v

/-- The target-ring formulation with coordinate multiplication written
explicitly instead of function-space scalar multiplication. -/
theorem eval₂_mul_of_isHomogeneous {f : MvPolynomial ι R} {d : ℕ}
    (hf : f.IsHomogeneous d) (φ : R →+* S) (c : S) (v : ι → S) :
    MvPolynomial.eval₂ φ (fun i => c * v i) f =
      c ^ d * MvPolynomial.eval₂ φ v f :=
  eval₂_smul_of_isHomogeneous hf φ c v

end OAI.AlgebraicGeometry.Foundations.Scheme.HomogeneousEvalMap
