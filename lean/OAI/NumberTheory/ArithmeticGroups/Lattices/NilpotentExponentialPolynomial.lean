import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-! # Nilpotent Exponential Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialPolynomial.Construction

noncomputable section

section

/-! Nilpotent endomorphisms have a dimension-uniform vanishing power,
so their exponential is a fixed finite polynomial. -/

open NormedSpace

theorem nilpotent_continuous_operator_pow_finrank
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (A : L →L[ℝ] L) (hA : IsNilpotent A) : A ^ Module.finrank ℝ L = 0 := by
  have hlin : IsNilpotent A.toLinearMap := hA.map ContinuousLinearMap.toLinearMapRingHom
  have hp : A.toLinearMap ^ Module.finrank ℝ L = 0 := by
    have he := A.toLinearMap.aeval_self_charpoly
    rwa [hlin.charpoly_eq_X_pow_finrank, map_pow, Polynomial.aeval_X] at he
  have he : ContinuousLinearMap.toLinearMapRingHom (A ^ Module.finrank ℝ L) = 0 := by
    rw [map_pow]
    exact hp
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun he x

theorem exp_eq_finite_sum_of_pow_eq_zero
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (X : A) (m : ℕ) (hm : X ^ m = 0) :
    exp X = ∑ i ∈ Finset.range m, (i.factorial⁻¹ : ℝ) • X ^ i := by
  rw [exp_eq_tsum ℝ]
  apply tsum_eq_sum
  intro i hi
  have hmi : m ≤ i := Nat.le_of_not_gt (fun h => hi (Finset.mem_range.mpr h))
  rw [pow_eq_zero_of_le hmi hm, smul_zero]

theorem positive_derivation_exponential_polynomial
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (X : L →L[ℝ] L) (hX : X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H) :
    exp X = ∑ i ∈ Finset.range (Module.finrank ℝ L), (i.factorial⁻¹ : ℝ) • X ^ i :=
  exp_eq_finite_sum_of_pow_eq_zero X (Module.finrank ℝ L)
    (nilpotent_continuous_operator_pow_finrank X (Positive.DerivationNilpotence.Construction.positiveBracketDerivations_isNilpotent B H hH X hX))

end

/-! A linear map whose difference from the identity is nilpotent has
determinant one. The same holds on every invariant subspace. -/

theorem linear_det_eq_one_of_unipotent
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (A : E →ₗ[ℝ] E) (hA : IsNilpotent (A - 1)) : A.det = 1 := by
  have hn : IsNilpotent (1 - A) := by simpa only [neg_sub] using hA.neg
  have he := (1 - A).eval_charpoly (1 : ℝ)
  rw [hn.charpoly_eq_X_pow_finrank] at he
  simpa using he.symm

theorem restrict_unipotent_linear_map
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ] E) (P : Submodule ℝ E) (hP : ∀ x ∈ P, A x ∈ P)
    (hA : IsNilpotent (A - 1)) : IsNilpotent (A.restrict hP - 1) := by
  obtain ⟨m, hm⟩ := hA
  refine ⟨m, ?_⟩
  have he : ∀ (n : ℕ) (x : P), (((A.restrict hP - 1) ^ n) x).val = ((A - 1) ^ n) x.val := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ']
      change A (((A.restrict hP - 1) ^ n) x).val - (((A.restrict hP - 1) ^ n) x).val = _
      rw [ih]
      rfl
  ext x
  rw [he, hm]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentExponentialPolynomial.Construction
