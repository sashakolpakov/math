import OAI.AlgebraicGeometry.Resolution.Blowups.SubsetCoordinateBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialBlowupChart

/-! # Subset Monomial Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SubsetMonomialTransform.Construction

noncomputable section

/-! Actual monomial controlled transforms for the minimal coordinate subsets selected by the algorithm. -/

open _root_.MvPolynomial Finset

universe u

variable {σ R : Type u} [CommRing R] [Fintype σ] [DecidableEq σ]

theorem coordinateMonomial_mem_subset_center_power (a : σ → ℕ) (C : Finset σ) :
    MonomialBlowupChart.Construction.coordinateMonomial (R := R) a ∈ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C ^ (∑ j ∈ C, a j) := by
  rw [← Finset.sum_ite_mem_eq C a, ← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro j _
  by_cases hj : j ∈ C
  · rw [ite_eq_left hj]
    exact Ideal.pow_mem_pow
      (show (X j : MvPolynomial σ R) ∈ SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C from Ideal.subset_span ⟨j, hj, rfl⟩) (a j)
  · rw [ite_eq_right hj, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- Only the exponents belonging to the selected center contribute to
the new exceptional exponent. All other coordinate factors are preserved. -/
theorem subsetCoordinateSubstitution_monomial (a : σ → ℕ) (C : Finset σ) (i : C) :
    SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution C i (MonomialBlowupChart.Construction.coordinateMonomial (R := R) a) =
      X i.val ^ (∑ j ∈ C, a j) * ∏ j ∈ univ.erase i.val, X j ^ a j := by
  rw [MonomialBlowupChart.Construction.coordinateMonomial, map_prod]
  have he : (∏ j, SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution (R := R) C i (X j ^ a j)) =
      ∏ j, (X i.val ^ (if j ∈ C then a j else 0) * if j = i.val then 1 else X j ^ a j) := by
    apply prod_congr rfl
    intro j _
    by_cases hji : j = i.val
    · subst j
      rw [map_pow, SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_self]
      simp [i.property]
    · by_cases hj : j ∈ C
      · rw [map_pow, SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_center C i j hji hj, mul_pow]
        simp [hj, hji]
      · rw [map_pow, SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_outside C i j hj]
        simp [hj, hji]
  rw [he, prod_mul_distrib, prod_pow_eq_pow_sum, sum_ite_mem_eq]
  congr 1
  rw [← mul_prod_erase univ (fun j => if j = i.val then 1 else (X j : MvPolynomial σ R) ^ a j)
    (mem_univ i.val), ite_eq_left rfl, one_mul]
  apply prod_congr rfl
  intro j hj
  rw [ite_eq_right (mem_erase.mp hj).1]

theorem subsetCoordinateMonomial_controlled_factorization (a : σ → ℕ) (b : ℕ)
    (C : Finset σ) (hb : b ≤ ∑ j ∈ C, a j) (i : C) :
    SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution C i (MonomialBlowupChart.Construction.coordinateMonomial (R := R) a) =
      X i.val ^ b * MonomialBlowupChart.Construction.coordinateMonomial (MonomialTermination.Construction.monomialChartExponents a b C i.val) := by
  rw [subsetCoordinateSubstitution_monomial, MonomialBlowupChart.Construction.coordinateMonomial,
    ← mul_prod_erase univ
      (fun j => X j ^ MonomialTermination.Construction.monomialChartExponents a b C i.val j) (mem_univ i.val)]
  have hi : MonomialTermination.Construction.monomialChartExponents a b C i.val i.val = (∑ j ∈ C, a j) - b := by
    simp [MonomialTermination.Construction.monomialChartExponents]
  have hrest : (∏ j ∈ univ.erase i.val,
      (X j : MvPolynomial σ R) ^ MonomialTermination.Construction.monomialChartExponents a b C i.val j) =
      ∏ j ∈ univ.erase i.val, X j ^ a j := by
    apply prod_congr rfl
    intro j hj
    simp only [MonomialTermination.Construction.monomialChartExponents, Function.update_of_ne (mem_erase.mp hj).1]
  rw [hi, hrest, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]

/-- The actual Rees controlled ideal has the selected-center exponent formula. -/
theorem subsetCoordinateMonomial_controlledIdeal (a : σ → ℕ) (b : ℕ)
    (C : Finset σ) (hb : b ≤ ∑ j ∈ C, a j) (i : C) :
    (ControlledTransform.Construction.blowupControlledTransform (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}) b
      (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).map (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial C i) =
        Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b C i.val)} := by
  let I := SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C
  let e : I := SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}
  let c := Blowup.Charts.Construction.blowupChartConstants I e e.val ^ b
  let φ := SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial (R := R) C i
  have hJ : J ≤ I ^ b := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_le_pow_right hb (coordinateMonomial_mem_subset_center_power a C)
  have hc : φ c = (X i.val : MvPolynomial σ R) ^ b := by
    change SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial (R := R) C i
      (Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i) (X i.val) ^ b) = _
    rw [map_pow (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial (R := R) C i)
      (Blowup.Charts.Construction.blowupChartConstants (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i) (X i.val)) b,
      SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial_constants, SubsetCoordinateBlowup.Construction.subsetCoordinateSubstitution_self]
  have hreg : IsRegular (φ c) := by
    rw [hc]
    exact (isRegular_X (R := R) (n := i.val)).pow b
  have htotal : (J.map (Blowup.Charts.Construction.blowupChartConstants I e)).map φ =
      Ideal.span {X i.val ^ b * MonomialBlowupChart.Construction.coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b C i.val)} := by
    change ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}).map (Blowup.Charts.Construction.blowupChartConstants I e)).map φ = _
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.comp_apply]
    rw [SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial_constants,
      subsetCoordinateMonomial_controlled_factorization a b C hb i]
  change ((J.map (Blowup.Charts.Construction.blowupChartConstants I e)).colon (Ideal.span {c})).map φ = _
  rw [ControlledTransformMap.Construction.map_colon_principal_of_divisible _ c φ
    (ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I J b e hJ) hreg, htotal, hc,
    ← Ideal.span_singleton_mul_span_singleton]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ ((isRegular_X (R := R) (n := i.val)).pow b)

/-- Every chart of every selected minimal center realizes a strict step
in the proved well-founded monomial exponent relation. -/
theorem minimal_subsetCoordinateMonomial_controlledIdeal_decreases (a : σ → ℕ) (b : ℕ)
    (C : Finset σ) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (i : C) :
    (ControlledTransform.Construction.blowupControlledTransform (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal (R := R) C) (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}) b
      (SubsetCoordinateBlowup.Construction.subsetCoordinateElement C i)).map (SubsetCoordinateBlowup.Construction.subsetCoordinateBlowupToPolynomial C i) =
        Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b C i.val)} ∧
      MonomialTermination.Construction.MonomialControlledStep b (MonomialTermination.Construction.monomialChartExponents a b C i.val) a :=
  ⟨subsetCoordinateMonomial_controlledIdeal a b C hC.2.1 i, ⟨C, i.val, hC, i.property, rfl⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SubsetMonomialTransform.Construction
