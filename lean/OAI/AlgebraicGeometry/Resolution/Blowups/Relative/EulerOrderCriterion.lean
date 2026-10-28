import OAI.AlgebraicGeometry.Resolution.Blowups.MappedEulerOrderCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Euler Order Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EulerOrderCriterion.Construction

noncomputable section

/-! Relative differential ideals detect actual local ideal powers using a coordinate frame. -/

variable {k A B ι : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra A B] [Algebra.FormallyEtale A B] [Algebra ℚ B]
  [Fintype ι] [DecidableEq ι]

/-- The coordinate Euler argument works with derivations over the fixed
coefficient ring, so the intrinsic relative differential ideals detect
the order of arbitrary ideals in the actual extended local ring. -/
theorem mapped_coordinate_order_iff_relative_differentialIdeal
    (z : ι → A) (D : ι → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (J : Ideal A) (b : ℕ) :
    J.map (algebraMap A B) ≤ Ideal.span (Set.range (fun i => algebraMap A B (z i))) ^ (b + 1) ↔
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b).map (algebraMap A B) ≤
        Ideal.span (Set.range (fun i => algebraMap A B (z i))) := by
  let w : ι → B := fun i => algebraMap A B (z i)
  let δ : ι → Derivation ℤ B B := fun i =>
    Etale.Derivation.Construction.extendEtaleRingDerivation (S := B) ((D i).restrictScalars ℤ)
  have hδ : ∀ i j, δ i (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, Derivation.restrictScalars_apply, hD]
    split_ifs <;> simp
  let M : Ideal B := Ideal.span (Set.range w)
  let E := EulerOrderCriterion.Construction.coordinateEulerDerivation w δ
  have hE : ∀ p, E p ∈ M := EulerOrderCriterion.Construction.coordinateEulerDerivation_mem_span w δ
  have hM : ∀ p ∈ M, E p - p ∈ M ^ 2 := by
    intro p hp
    apply EulerOrderCriterion.Construction.euler_span_mod_square E (Set.range w) _ hE hp
    rintro x ⟨i, rfl⟩
    exact EulerOrderCriterion.Construction.coordinateEulerDerivation_coordinate w δ hδ i
  change J.map (algebraMap A B) ≤ M ^ (b + 1) ↔
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J b).map (algebraMap A B) ≤ M
  constructor
  · intro h
    apply (Ideal.map_mono (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J b)).trans
    apply (Etale.Derivation.Construction.iteratedDifferentialIdeal_map_le_of_etale (S := B) J b).trans
    simpa only [pow_one] using DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow M (J.map (algebraMap A B)) 1 b
      (by simpa only [Nat.add_comm 1 b] using h)
  · induction b generalizing J with
    | zero =>
      intro h
      simpa only [DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, zero_add, pow_one] using h
    | succ b ih =>
      intro h
      have hfirst : (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map (algebraMap A B) ≤ M ^ (b + 1) :=
        ih (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J) h
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change algebraMap A B p ∈ M ^ (b + 1 + 1)
      have hpM : algebraMap A B p ∈ M ^ (b + 1) :=
        hfirst (Ideal.mem_map_of_mem _ (DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J hp))
      have hEp : E (algebraMap A B p) ∈ M ^ (b + 1 + 1) := by
        rw [EulerOrderCriterion.Construction.coordinateEulerDerivation_apply]
        apply Ideal.sum_mem
        intro i _
        have hdp : δ i (algebraMap A B p) ∈ M ^ (b + 1) := by
          rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, Derivation.restrictScalars_apply]
          exact hfirst (Ideal.mem_map_of_mem _ (DifferentialBlowup.Construction.relative_derivation_mem_first k J (D i) hp))
        rw [pow_succ']
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) hdp
      have hcong := EulerOrderCriterion.Construction.euler_ideal_power_congruence E M hE hM (b + 1) hpM
      have hnp : (b + 1) • algebraMap A B p ∈ M ^ (b + 1 + 1) := by
        simpa only [sub_sub_cancel] using (M ^ (b + 1 + 1)).sub_mem hEp hcong
      obtain ⟨u, hu⟩ := DifferentialCoefficientOrder.Construction.natCast_isUnit_of_rationalAlgebra (A := B) (b + 1) (by omega)
      rw [nsmul_eq_mul, ← hu] at hnp
      have hmul := (M ^ (b + 1 + 1)).mul_mem_left (u⁻¹ : Bˣ) hnp
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hmul

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EulerOrderCriterion.Construction
