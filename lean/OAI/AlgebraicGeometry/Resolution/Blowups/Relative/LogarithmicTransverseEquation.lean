import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ModuleDerivations
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualDropAllPrimes

/-! # Logarithmic Transverse Equation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransverseEquation.Construction

noncomputable section

/-! Relative coordinate derivations detect a transverse logarithmic direction at every prime. -/

variable {σ k A : Type*} [Field k] [CommRing A] [Fintype σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ k) A] [Algebra.Etale (MvPolynomial σ k) A]
  [Algebra k A] [IsScalarTower k (MvPolynomial σ k) A]

/-- The relative coordinate basis detects an outside direction without
requiring the prime to be a closed or rational point. -/
theorem relative_logarithmic_derivative_detects_transverse_direction
    (B : Finset σ) (q : Ideal A)
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ k) A (MvPolynomial.X i) ∈ q)
    (E : Derivation k A A)
    (hE : ∀ i ∈ B, E (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)})
    (z : A) (hEz : E z ∉ q) :
    ∃ i : σ, i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i z ∉ q := by
  classical
  by_contra hoff
  push Not at hoff
  apply hEz
  rw [Blowups.Etale.ModuleDerivations.Construction.etale_relative_derivation_apply (σ := σ) E z]
  apply Ideal.sum_mem
  intro i _
  by_cases hi : i ∈ B
  · have hcoef : E (algebraMap (MvPolynomial σ k) A (MvPolynomial.X i)) ∈ q :=
      (Ideal.span_singleton_le_iff_mem q).mpr (hB i hi) (hE i hi)
    exact q.mul_mem_right _ hcoef
  · exact q.mul_mem_left _ (hoff i hi)

/-- A positive local-order condition and a relative logarithmic unit
bound produce a differential equation transverse to every active
coordinate boundary, at any prime and in any characteristic. -/
theorem exists_etale_relative_logarithmic_transverse_equation
    (B : Finset σ) (q : Ideal A) [q.IsPrime]
    (hB : ∀ i ∈ B, algebraMap (MvPolynomial σ k) A (MvPolynomial.X i) ∈ q)
    (J : Ideal A) (n : ℕ)
    (hJ : J.map (algebraMap A (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1))
    (hbound : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
      (fun i : B => algebraMap (MvPolynomial σ k) A (MvPolynomial.X i.val)) J (n + 1) = ⊤) :
    ∃ (z : A) (i : σ),
      z ∈ LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
          (fun j : B => algebraMap (MvPolynomial σ k) A (MvPolynomial.X j.val)) J n ∧
      z ∈ q ∧ i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := A) i z ∉ q := by
  classical
  let w : B → A := fun i => algebraMap (MvPolynomial σ k) A (MvPolynomial.X i.val)
  let H := LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n
  have hrel : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ q := by
    simpa only [Nat.add_sub_cancel] using
      ResidualDropAllPrimes.Construction.relative_differential_control_le_prime_of_local_order k J q (n + 1) (Nat.zero_lt_succ n) hJ
  have hH : H ≤ q := (LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_le_relative k w J n).trans hrel
  have hex : ∃ (E : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (z : A), z ∈ H ∧ E.val z ∉ q := by
    by_contra h
    push Not at h
    have hle : LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w H ≤ q := by
      apply sup_le hH
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨E, z⟩, rfl⟩
      exact h E z.val z.property
    change LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w
      (LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n) ≤ q at hle
    rw [LogarithmicIdeal.Construction.first_iteratedRelativeLogarithmicDifferentialIdeal, hbound] at hle
    exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp hle)
  obtain ⟨E, z, hz, hEz⟩ := hex
  obtain ⟨i, hi, hiz⟩ := relative_logarithmic_derivative_detects_transverse_direction
    B q hB E.val (fun j hj => E.property ⟨j, hj⟩) z hEz
  exact ⟨z, i, hz, hH hz, hi, hiz⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransverseEquation.Construction
