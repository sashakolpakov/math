import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Weighted Coefficient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientTransform.Construction

noncomputable section

/-! Exact compatibility of weighted coefficient ideals with actual controlled transforms. -/

variable {R : Type*} [CommRing R]

/-- Exceptional factors in the separate coefficients become a common
exceptional factor of exponent `b!` in their weighted sum. -/
theorem weightedCoefficientIdeal_factorization (c : R) (b : ℕ)
    (J T : Fin b → Ideal R)
    (h : ∀ j, J j = Ideal.span {c ^ (b - j.val)} * T j) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J = Ideal.span {c ^ b.factorial} * WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b T := by
  simp only [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal, Ideal.mul_iSup]
  congr 1
  funext j
  rw [h j, mul_pow, Ideal.span_singleton_pow, ← pow_mul, WeightedCoefficientIdeal.Construction.coefficientWeight_mul_control]

/-- Taking a common controlled quotient agrees with taking the separate
coefficient quotients before weighting. -/
theorem weightedCoefficientIdeal_colon (c : R) (hc : IsRegular c) (b : ℕ)
    (J : Fin b → Ideal R) (hJ : ∀ j, J j ≤ Ideal.span {c ^ (b - j.val)}) :
    (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J).colon (Ideal.span {c ^ b.factorial}) =
      WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => (J j).colon (Ideal.span {c ^ (b - j.val)})) := by
  rw [weightedCoefficientIdeal_factorization c b J
    (fun j => (J j).colon (Ideal.span {c ^ (b - j.val)}))
    (fun j => (ControlledTransform.Construction.principal_mul_colon_of_le (J j) (c ^ (b - j.val)) (hJ j)).symm)]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (hc.pow b.factorial)

/-- The weighted ideal is permissible for every center permissible for
all of its coefficient conditions. -/
theorem weightedCoefficientIdeal_permissible (I : Ideal R) (b : ℕ)
    (J : Fin b → Ideal R) (hJ : ∀ j, J j ≤ I ^ (b - j.val)) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ I ^ b.factorial :=
  WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow I b J hJ

/-- On each actual Rees blowup chart, controlled transform commutes
exactly with forming the weighted coefficient ideal. -/
theorem blowup_weightedCoefficientIdeal_controlledTransform (I : Ideal R) (b : ℕ)
    (J : Fin b → Ideal R) (a : I) (hJ : ∀ j, J j ≤ I ^ (b - j.val)) :
    ControlledTransform.Construction.blowupControlledTransform I (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J) b.factorial a =
      WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => ControlledTransform.Construction.blowupControlledTransform I (J j) (b - j.val) a) := by
  unfold ControlledTransform.Construction.blowupControlledTransform
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  exact weightedCoefficientIdeal_colon (Blowup.Charts.Construction.blowupChartConstants I a a.val)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) b _
    (fun j => ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I (J j) (b - j.val) a (hJ j))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientTransform.Construction
