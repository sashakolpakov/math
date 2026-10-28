import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Polynomial.DividedPolynomial

noncomputable section

/-!
# Cohomology: the one-variable divided-power Poincaré calculation

The coefficient module with basis `T^[n]` has differential
`d(T^[n+1]) = T^[n] dT` and a coefficient-shift primitive. We prove the
contracting identity integrally, then identify this differential with the
ordinary polynomial derivative under `T^[n] ↦ T^n/n!` in characteristic zero.
This is a local calculation, not the global crystalline comparison theorem.
-/

variable (R : Type*) [CommRing R]

/-- Coefficients in the divided-monomial basis. -/
abbrev Coefficients := ℕ →₀ R

/-- Differentiation lowers the divided-monomial degree. -/
def differential : Coefficients R →ₗ[R] Coefficients R :=
  Finsupp.lcomapDomain Nat.succ Nat.succ_injective

/-- Integration raises the divided-monomial degree, without division in `R`. -/
def primitive : Coefficients R →ₗ[R] Coefficients R :=
  Finsupp.lmapDomain R R Nat.succ

/-- Include coefficients as constant divided polynomials. -/
def constant : R →ₗ[R] Coefficients R := Finsupp.lsingle 0

/-- The constant coefficient. -/
def evaluation : Coefficients R →ₗ[R] R := Finsupp.lapply 0

@[simp]
theorem differential_apply (f : Coefficients R) (n : ℕ) :
    differential R f n = f (n + 1) := rfl

@[simp]
theorem primitive_zero (f : Coefficients R) : primitive R f 0 = 0 := by
  exact Finsupp.mapDomain_of_notMem_range f 0 (by simp)

@[simp]
theorem primitive_succ (f : Coefficients R) (n : ℕ) :
    primitive R f (n + 1) = f n :=
  Finsupp.mapDomain_apply_of_injective Nat.succ_injective f n

/-- Every divided-polynomial one-form has an integral primitive. -/
@[simp]
theorem differential_primitive (f : Coefficients R) :
    differential R (primitive R f) = f := by
  ext n
  simp

/-- The integral contracting identity for degree-zero forms. -/
theorem primitive_differential (f : Coefficients R) :
    primitive R (differential R f) + Finsupp.single 0 (f 0) = f := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp

/-- Closed divided polynomials are precisely constants. -/
theorem differential_eq_zero_iff (f : Coefficients R) :
    differential R f = 0 ↔ f = Finsupp.single 0 (f 0) := by
  constructor
  · intro hf
    simpa only [hf, map_zero, zero_add] using (primitive_differential R f).symm
  · intro hf
    ext n
    rw [differential_apply, hf]
    simp

theorem differential_surjective : Function.Surjective (differential R) :=
  fun f => ⟨primitive R f, differential_primitive R f⟩

section Completion

variable (I : Ideal R)

/-- The primitive remains a right inverse after adic completion. -/
theorem completed_differential_primitive
    (f : AdicCompletion I (Coefficients R)) :
    AdicCompletion.map I (differential R)
      (AdicCompletion.map I (primitive R) f) = f := by
  rw [AdicCompletion.map_comp_apply]
  have h : (differential R).comp (primitive R) = LinearMap.id :=
    LinearMap.ext (differential_primitive R)
  rw [h, AdicCompletion.map_id, LinearMap.id_apply]

/-- The contracting identity survives completion, including its constants. -/
theorem completed_primitive_differential
    (f : AdicCompletion I (Coefficients R)) :
    AdicCompletion.map I (primitive R)
        (AdicCompletion.map I (differential R) f) +
      AdicCompletion.map I (constant R)
        (AdicCompletion.map I (evaluation R) f) = f := by
  induction f using AdicCompletion.induction_on with
  | _ a =>
    simp only [AdicCompletion.map_mk]
    rw [← map_add]
    congr 1
    apply Subtype.ext
    funext n
    exact primitive_differential R (a n)

/-- The completed differential is surjective. -/
theorem completed_differential_surjective :
    Function.Surjective (AdicCompletion.map I (differential R)) :=
  fun f => ⟨AdicCompletion.map I (primitive R) f,
    completed_differential_primitive R I f⟩

/-- The kernel of the completed differential consists of completed constants. -/
theorem completed_differential_eq_zero_iff
    (f : AdicCompletion I (Coefficients R)) :
    AdicCompletion.map I (differential R) f = 0 ↔
      ∃ a : AdicCompletion I R, AdicCompletion.map I (constant R) a = f := by
  constructor
  · intro hf
    refine ⟨AdicCompletion.map I (evaluation R) f, ?_⟩
    simpa only [hf, map_zero, zero_add] using completed_primitive_differential R I f
  · rintro ⟨a, rfl⟩
    rw [AdicCompletion.map_comp_apply]
    have h : (differential R).comp (constant R) = 0 := by
      apply LinearMap.ext
      intro a
      ext n
      simp [constant, differential]
    rw [h, AdicCompletion.map_zero, LinearMap.zero_apply]

end Completion

variable (K : Type*) [Field K] [CharZero K] [Algebra R K]

/-- Realize divided monomials as actual polynomials over the fraction field. -/
def toPolynomial : Coefficients R →ₗ[R] Polynomial K :=
  Finsupp.linearCombination R
    (fun n : ℕ => Polynomial.monomial n ((n.factorial : K)⁻¹))

omit [CharZero K] in
@[simp]
theorem toPolynomial_single (n : ℕ) (a : R) :
    toPolynomial R K (Finsupp.single n a) =
      a • Polynomial.monomial n ((n.factorial : K)⁻¹) := by
  simp [toPolynomial]

omit [CharZero K] in
/-- The coefficient realization is the expected factorial normalization. -/
theorem coeff_toPolynomial (f : Coefficients R) (n : ℕ) :
    (toPolynomial R K f).coeff n =
      algebraMap R K (f n) / (n.factorial : K) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add f g hf hg =>
    simp only [map_add, Polynomial.coeff_add, Finsupp.add_apply, hf, hg, add_div]
  | single m a =>
    by_cases h : m = n
    · subst m
      simp [toPolynomial_single, Algebra.smul_def, div_eq_mul_inv]
    · simp [toPolynomial_single, Polynomial.coeff_smul, Polynomial.coeff_monomial,
        h, Ne.symm h]

/-- For an injective coefficient map, the divided-polynomial realization is faithful. -/
theorem toPolynomial_injective (h : Function.Injective (algebraMap R K)) :
    Function.Injective (toPolynomial R K) := by
  intro f g hfg
  ext n
  apply h
  have hn : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have heq := congrArg (fun q : Polynomial K => q.coeff n) hfg
  rw [coeff_toPolynomial, coeff_toPolynomial] at heq
  exact (div_left_inj' hn).mp heq

/-- The coefficient-shift differential is the actual polynomial derivative. -/
theorem derivative_toPolynomial (f : Coefficients R) :
    (toPolynomial R K f).derivative = toPolynomial R K (differential R f) := by
  ext n
  rw [Polynomial.coeff_derivative, coeff_toPolynomial, coeff_toPolynomial,
    differential_apply, Nat.factorial_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp
  simp

/-- Differentiation preserves the integral divided-polynomial submodule. -/
theorem derivative_mem_range (q : Polynomial K)
    (hq : q ∈ LinearMap.range (toPolynomial R K)) :
    q.derivative ∈ LinearMap.range (toPolynomial R K) := by
  obtain ⟨f, rfl⟩ := hq
  exact ⟨differential R f, (derivative_toPolynomial R K f).symm⟩

/-- Integral divided polynomials admit integral divided-polynomial primitives. -/
theorem exists_primitive_in_range (q : Polynomial K)
    (hq : q ∈ LinearMap.range (toPolynomial R K)) :
    ∃ Q ∈ LinearMap.range (toPolynomial R K), Q.derivative = q := by
  obtain ⟨f, rfl⟩ := hq
  refine ⟨toPolynomial R K (primitive R f), ⟨primitive R f, rfl⟩, ?_⟩
  rw [derivative_toPolynomial, differential_primitive]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.Polynomial.DividedPolynomial
