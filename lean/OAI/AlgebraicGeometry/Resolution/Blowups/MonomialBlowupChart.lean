import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap
import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTermination

/-! # Monomial Blowup Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MonomialBlowupChart.Construction

noncomputable section

/-! Monomial controlled transforms on the actual Rees charts of coordinate blowups. -/

open _root_.MvPolynomial Finset

universe u

variable {σ R : Type u} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- A coordinate monomial, expressed as a product to record its exponent vector. -/
def coordinateMonomial (a : σ → ℕ) : MvPolynomial σ R := ∏ j, X j ^ a j

omit [DecidableEq σ] in
theorem coordinateMonomial_mem_center_power (a : σ → ℕ) :
    coordinateMonomial (R := R) a ∈ idealOfVars σ R ^ (∑ j, a j) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Ideal.prod_mem_prod
  intro j _
  exact Ideal.pow_mem_pow
    (show (X j : MvPolynomial σ R) ∈ idealOfVars σ R from Ideal.subset_span ⟨j, rfl⟩) (a j)

/-- Under the actual chart substitution, all center exponents contribute
to the exceptional coordinate. -/
theorem coordinateBlowupSubstitution_monomial (a : σ → ℕ) (i : σ) :
    Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution i (coordinateMonomial (R := R) a) =
      X i ^ (∑ j, a j) * ∏ j ∈ univ.erase i, X j ^ a j := by
  rw [coordinateMonomial, map_prod,
    ← mul_prod_erase univ (fun j => Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution i (X j ^ a j)) (mem_univ i),
    map_pow, Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution_X_self]
  have he : (∏ j ∈ univ.erase i, Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution (R := R) i (X j ^ a j)) =
      X i ^ (∑ j ∈ univ.erase i, a j) * ∏ j ∈ univ.erase i, X j ^ a j := by
    calc
      _ = ∏ j ∈ univ.erase i, (X i ^ a j * X j ^ a j) := by
        apply prod_congr rfl
        intro j hj
        rw [map_pow, Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution_X_ne i j (mem_erase.mp hj).1, mul_pow]
      _ = _ := by rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [he, ← mul_assoc, ← pow_add, add_sum_erase univ a (mem_univ i)]

/-- Dividing by the prescribed exceptional power gives the explicit
controlled exponent update, with no formal chart placeholders. -/
theorem coordinateMonomial_controlled_factorization (a : σ → ℕ) (b : ℕ)
    (hb : b ≤ ∑ j, a j) (i : σ) :
    Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution i (coordinateMonomial (R := R) a) =
      X i ^ b * coordinateMonomial (MonomialTermination.Construction.monomialChartExponents a b univ i) := by
  rw [coordinateBlowupSubstitution_monomial, coordinateMonomial,
    ← mul_prod_erase univ
      (fun j => X j ^ MonomialTermination.Construction.monomialChartExponents a b univ i j) (mem_univ i)]
  have hi : MonomialTermination.Construction.monomialChartExponents a b univ i i = (∑ j, a j) - b := by
    simp [MonomialTermination.Construction.monomialChartExponents]
  have hrest : (∏ j ∈ univ.erase i, (X j : MvPolynomial σ R) ^ MonomialTermination.Construction.monomialChartExponents a b univ i j) =
      ∏ j ∈ univ.erase i, X j ^ a j := by
    apply prod_congr rfl
    intro j hj
    simp only [MonomialTermination.Construction.monomialChartExponents, Function.update_of_ne (mem_erase.mp hj).1]
  rw [hi, hrest, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hb]

/-- The ideal quotient defining the actual controlled transform is exactly
the principal ideal of the updated monomial under the chart isomorphism. -/
theorem coordinateMonomial_controlledIdeal (a : σ → ℕ) (b : ℕ)
    (hb : b ≤ ∑ j, a j) (i : σ) :
    (ControlledTransform.Construction.blowupControlledTransform (idealOfVars σ R) (Ideal.span {coordinateMonomial a}) b
      (Coordinate.CenterBlowup.Construction.coordinateCenterElement i)).map (Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial i) =
        Ideal.span {coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b univ i)} := by
  let I := idealOfVars σ R
  let e : I := Coordinate.CenterBlowup.Construction.coordinateCenterElement i
  let J : Ideal (MvPolynomial σ R) := Ideal.span {coordinateMonomial a}
  let c := Blowup.Charts.Construction.blowupChartConstants I e e.val ^ b
  let φ := Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial (R := R) i
  have hJ : J ≤ I ^ b := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_le_pow_right hb (coordinateMonomial_mem_center_power a)
  have hc : φ c = (X i : MvPolynomial σ R) ^ b := by
    change Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial i
      (Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i) (X i) ^ b) = _
    rw [map_pow (Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial (R := R) i)
      (Blowup.Charts.Construction.blowupChartConstants (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i) (X i)) b,
      Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial_constants, Coordinate.CenterBlowup.Construction.coordinateBlowupSubstitution_X_self]
  have hreg : IsRegular (φ c) := by
    rw [hc]
    exact (isRegular_X (R := R) (n := i)).pow b
  have htotal : (J.map (Blowup.Charts.Construction.blowupChartConstants I e)).map φ =
      Ideal.span {X i ^ b * coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b univ i)} := by
    change ((Ideal.span {coordinateMonomial a}).map (Blowup.Charts.Construction.blowupChartConstants I e)).map φ = _
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton, RingHom.comp_apply]
    rw [Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial_constants, coordinateMonomial_controlled_factorization a b hb i]
  change ((J.map (Blowup.Charts.Construction.blowupChartConstants I e)).colon (Ideal.span {c})).map φ = _
  rw [ControlledTransformMap.Construction.map_colon_principal_of_divisible _ c φ
    (ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I J b e hJ) hreg, htotal, hc,
    ← Ideal.span_singleton_mul_span_singleton]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ ((isRegular_X (R := R) (n := i)).pow b)

/-- At a minimal coordinate center, the actual controlled ideal is monomial
with strictly smaller total exponent in every actual Rees chart. -/
theorem coordinateMonomial_controlledIdeal_decreases (a : σ → ℕ) (b : ℕ)
    (hC : MonomialTermination.Construction.MinimalMonomialCenter a b univ) (i : σ) :
    (ControlledTransform.Construction.blowupControlledTransform (idealOfVars σ R) (Ideal.span {coordinateMonomial a}) b
      (Coordinate.CenterBlowup.Construction.coordinateCenterElement i)).map (Coordinate.CenterBlowup.Construction.coordinateBlowupToPolynomial i) =
        Ideal.span {coordinateMonomial (R := R) (MonomialTermination.Construction.monomialChartExponents a b univ i)} ∧
      (∑ j, MonomialTermination.Construction.monomialChartExponents a b univ i j) < ∑ j, a j :=
  ⟨coordinateMonomial_controlledIdeal a b hC.2.1 i,
    MonomialTermination.Construction.monomialChartExponents_sum_lt a b univ hC i (mem_univ i)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MonomialBlowupChart.Construction
