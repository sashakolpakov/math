import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-!
# Finite coefficient-weighted moment extraction

The exponent used as a moment weight and the exponent used for coefficient
extraction are independent until the final diagonal sum.  The only support
hypothesis is containment of each input polynomial's support in the retained
finite index set.  In particular no independence of monomial functions on the
finite input set is assumed.

An additive-map corollary permits a final linear operation on canonical
representatives, such as evaluating the retained U polynomial at one.  It does
not assert that this operation is multiplicative on a truncated quotient.
-/

namespace SubexponentialSAT.Moments

noncomputable section

open scoped BigOperators

variable {ι τ R S : Type*} [CommSemiring R]

/-- Each coordinate exponent is bounded by the total exponent. -/
theorem exponent_le_total (a : ι →₀ ℕ) (i : ι) :
    a i ≤ a.sum (fun _ n => n) := by
  classical
  by_cases hi : a i = 0
  · simp [hi]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hi)

/-- The finite set of exponents of total degree at most `N`.

This is a denotational finite-set construction; no runtime claim is made for
enumerating this set via the auxiliary coordinate box used in this definition.
-/
def retained [Fintype ι] (N : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.univ.image fun f : ι → Fin (N + 1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (f i).val)).filter
      (fun a => a.sum (fun _ n => n) ≤ N)

@[simp] theorem mem_retained [Fintype ι] (N : ℕ) (a : ι →₀ ℕ) :
    a ∈ retained N ↔ a.sum (fun _ n => n) ≤ N := by
  classical
  simp only [retained, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro ha
    refine ⟨Finset.mem_image.mpr ?_, ha⟩
    refine ⟨(fun i => ⟨a i, Nat.lt_succ_of_le ((exponent_le_total a i).trans ha)⟩),
      Finset.mem_univ _, ?_⟩
    ext i
    rfl

theorem support_subset_retained [Fintype ι] (N : ℕ)
    (A : MvPolynomial ι R) (hA : A.totalDegree ≤ N) :
    A.support ⊆ retained N := by
  intro a ha
  exact (mem_retained N a).mpr ((MvPolynomial.le_totalDegree ha).trans hA)

/-- The scalar monomial weight at an input valuation. -/
def weight (a : ι →₀ ℕ) (v : ι → R) : R :=
  ∏ i ∈ a.support, v i ^ a i

theorem weight_eq_prod_univ [Fintype ι] (a : ι →₀ ℕ) (v : ι → R) :
    weight a v = ∏ i, v i ^ a i := by
  exact Finsupp.prod_pow a v

/-- A polynomial-valued moment; the moment index is not a formal variable. -/
def moment (s : Finset τ) (A : τ → MvPolynomial ι R)
    (v : τ → ι → R) (a : ι →₀ ℕ) : MvPolynomial ι R :=
  ∑ x ∈ s, MvPolynomial.C (weight a (v x)) * A x

/-- Coefficient and moment indices need not agree. -/
theorem coeff_moment (s : Finset τ) (A : τ → MvPolynomial ι R)
    (v : τ → ι → R) (a b : ι →₀ ℕ) :
    (moment s A v a).coeff b =
      ∑ x ∈ s, weight a (v x) * (A x).coeff b := by
  simp only [moment, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

/-- Evaluation is the coefficient-weighted sum over any retained set containing
the polynomial support.  Extra retained indices contribute zero. -/
theorem sum_weight_coeff_eq_eval (M : Finset (ι →₀ ℕ))
    (A : MvPolynomial ι R) (v : ι → R) (hA : A.support ⊆ M) :
    (∑ a ∈ M, weight a v * A.coeff a) =
      MvPolynomial.eval v A := by
  classical
  rw [MvPolynomial.eval_eq]
  symm
  calc
    (∑ a ∈ A.support, A.coeff a *
        ∏ i ∈ a.support, v i ^ a i) =
        ∑ a ∈ M, A.coeff a *
          ∏ i ∈ a.support, v i ^ a i := by
      apply Finset.sum_subset hA
      intro a _ ha
      simp [MvPolynomial.notMem_support_iff.mp ha]
    _ = ∑ a ∈ M, weight a v * A.coeff a := by
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _

/-- Equations (4.6)-(4.7): the diagonal of all coefficient-weighted moments
recovers the sum of input-dependent polynomial evaluations. -/
theorem sum_coeff_moment_eq_sum_eval (s : Finset τ)
    (M : Finset (ι →₀ ℕ)) (A : τ → MvPolynomial ι R)
    (v : τ → ι → R) (hA : ∀ x ∈ s, (A x).support ⊆ M) :
    (∑ a ∈ M, (moment s A v a).coeff a) =
      ∑ x ∈ s, MvPolynomial.eval (v x) (A x) := by
  simp_rw [coeff_moment]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x hx =>
    sum_weight_coeff_eq_eval M (A x) (v x) (hA x hx)

/-- The concrete degree hypothesis used by canonical truncation supplies the
support condition.  `M` may be any finite set containing all exponents through
degree `N`, including the manuscript's retained monomial list. -/
theorem sum_coeff_moment_eq_sum_eval_of_totalDegree_le (N : ℕ)
    (s : Finset τ) (M : Finset (ι →₀ ℕ))
    (A : τ → MvPolynomial ι R) (v : τ → ι → R)
    (hM : ∀ a : ι →₀ ℕ, a.sum (fun _ n => n) ≤ N → a ∈ M)
    (hA : ∀ x ∈ s, (A x).totalDegree ≤ N) :
    (∑ a ∈ M, (moment s A v a).coeff a) =
      ∑ x ∈ s, MvPolynomial.eval (v x) (A x) := by
  apply sum_coeff_moment_eq_sum_eval
  intro x hx a ha
  exact hM a ((MvPolynomial.le_totalDegree ha).trans (hA x hx))

/-- The manuscript's degree-bounded moment extraction, with the finite retained
index set constructed explicitly. -/
theorem sum_retained_coeff_moment_eq_sum_eval [Fintype ι] (N : ℕ)
    (s : Finset τ) (A : τ → MvPolynomial ι R) (v : τ → ι → R)
    (hA : ∀ x ∈ s, (A x).totalDegree ≤ N) :
    (∑ a ∈ retained N, (moment s A v a).coeff a) =
      ∑ x ∈ s, MvPolynomial.eval (v x) (A x) :=
  sum_coeff_moment_eq_sum_eval s (retained N) A v
    (fun x hx => support_subset_retained N (A x) (hA x hx))

/-- Any additive map may be applied after canonical coefficient extraction.
Only additivity, not multiplicativity, is needed for the last operation. -/
theorem sum_map_coeff_moment_eq_sum_map_eval [AddCommMonoid S]
    (L : R →+ S) (s : Finset τ) (M : Finset (ι →₀ ℕ))
    (A : τ → MvPolynomial ι R) (v : τ → ι → R)
    (hA : ∀ x ∈ s, (A x).support ⊆ M) :
    (∑ a ∈ M, L ((moment s A v a).coeff a)) =
      ∑ x ∈ s, L (MvPolynomial.eval (v x) (A x)) := by
  simpa only [map_sum] using
    congrArg L (sum_coeff_moment_eq_sum_eval s M A v hA)

/-- The last operation in (4.7), on genuine polynomial representatives.
Taking U = 1 is used only after forming the complete moments. -/
theorem sum_eval_one_coeff_moment_eq_sum_eval_one_eval
    (s : Finset τ) (M : Finset (ι →₀ ℕ))
    (A : τ → MvPolynomial ι (Polynomial R)) (v : τ → ι → R)
    (hA : ∀ x ∈ s, (A x).support ⊆ M) :
    (∑ a ∈ M, ((moment s A (fun x i => Polynomial.C (v x i)) a).coeff a).eval 1) =
      ∑ x ∈ s,
        (MvPolynomial.eval (fun i => Polynomial.C (v x i)) (A x)).eval 1 := by
  exact sum_map_coeff_moment_eq_sum_map_eval
    (Polynomial.evalRingHom (1 : R)).toAddMonoidHom s M A
    (fun x i => Polynomial.C (v x i)) hA

/-- A coefficientwise interface for nested polynomial representations.
The finite slots may, for example, be the retained U exponents at a fixed Z
coefficient.  Summing slots commutes with the complete moment calculation. -/
theorem sum_slots_coeff_moment_eq_sum_slots_eval {κ : Type*}
    (s : Finset τ) (M : Finset (ι →₀ ℕ)) (J : Finset κ)
    (A : τ → κ → MvPolynomial ι R) (v : τ → ι → R)
    (hA : ∀ x ∈ s, ∀ j ∈ J, (A x j).support ⊆ M) :
    (∑ a ∈ M, ∑ j ∈ J, (moment s (fun x => A x j) v a).coeff a) =
      ∑ x ∈ s, ∑ j ∈ J, MvPolynomial.eval (v x) (A x j) := by
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ J, ∑ a ∈ M, (moment s (fun x => A x j) v a).coeff a) =
        ∑ j ∈ J, ∑ x ∈ s, MvPolynomial.eval (v x) (A x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_coeff_moment_eq_sum_eval s M (fun x => A x j) v
        (fun x hx => hA x hx j hj)
    _ = _ := Finset.sum_comm

/-- Whole-polynomial moment extraction with U outermost, Z in the middle,
and the X variables innermost.  This is the representation used by Truncation.
Both U and Z remain formal in this identity. -/
theorem sum_nested_moments_eq_sum_substX
    (s : Finset τ) (M : Finset (ι →₀ ℕ))
    (A : τ → Truncation.Poly ι R) (v : τ → ι → R)
    (hA : ∀ x ∈ s, ∀ j r, (((A x).coeff j).coeff r).support ⊆ M) :
    (∑ a ∈ M,
      Truncation.mapCoeffs
        (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a))
        (∑ x ∈ s, WeightedSupport.scalarHom (weight a (v x)) * A x)) =
      ∑ x ∈ s, Truncation.substX (v x) (A x) := by
  ext j r
  simpa only [Polynomial.finsetSum_coeff, Truncation.coeff_mapCoeffs,
    MvPolynomial.coeffAddMonoidHom_apply, WeightedSupport.scalarHom_apply,
    Polynomial.coeff_C_mul, Truncation.coeff_substX, moment] using
    (sum_coeff_moment_eq_sum_eval s M (fun x => ((A x).coeff j).coeff r) v
      (fun x hx => hA x hx j r))

/-- The whole-polynomial form of (4.6)-(4.7), including U = 1 only after
the full canonical moments have been formed and their X coefficients extracted. -/
theorem sum_nested_moments_eval_one_eq_sum_evalXU
    (s : Finset τ) (M : Finset (ι →₀ ℕ))
    (A : τ → Truncation.Poly ι R) (v : τ → ι → R)
    (hA : ∀ x ∈ s, ∀ j r, (((A x).coeff j).coeff r).support ⊆ M) :
    (∑ a ∈ M,
      (Truncation.mapCoeffs
        (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a))
        (∑ x ∈ s, WeightedSupport.scalarHom (weight a (v x)) * A x)).eval 1) =
      ∑ x ∈ s, Truncation.evalXU (v x) (A x) := by
  have h := congrArg (Polynomial.evalRingHom (1 : Polynomial R))
    (sum_nested_moments_eq_sum_substX s M A v hA)
  simpa only [map_sum, Polynomial.coe_evalRingHom, Polynomial.eval_finsetSum,
    Truncation.evalXU_apply] using h

/-- The finite-type, degree-cutoff interface used by the counting module. -/
theorem sum_retained_nested_moments_eval_one_eq_sum_evalXU
    [Fintype ι] [Fintype τ] (N : ℕ)
    (A : τ → Truncation.Poly ι R) (v : τ → ι → R)
    (hA : ∀ x j r, (((A x).coeff j).coeff r).support ⊆ retained N) :
    (∑ a ∈ retained N,
      (Truncation.mapCoeffs
        (Truncation.mapCoeffs (MvPolynomial.coeffAddMonoidHom a))
        (∑ x, WeightedSupport.scalarHom (weight a (v x)) * A x)).eval 1) =
      ∑ x, Truncation.evalXU (v x) (A x) :=
  sum_nested_moments_eval_one_eq_sum_evalXU Finset.univ (retained N) A v
    (fun x _ => hA x)

end

end SubexponentialSAT.Moments

end OAI.Algorithms
