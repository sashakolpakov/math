import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialBlowupTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTransformIdeals

/-! # Blowup Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupTransform.Construction

noncomputable section

/-!
Coordinate derivations on blowup charts whose denominator has derivative zero.
These identities apply to actual Rees charts and their divided sections.
-/

universe u

variable {R : Type u} [CommRing R]

private theorem quotient_rule_identity (c x y v w : R)
    (h : c * x + w * (c * y) = c * v) : c * x = c * (v - y * w) := by
  linear_combination h

/-- The lifted derivation differentiates a chart ratio by the quotient rule. -/
theorem blowupChartDerivation_ratio (I : Ideal R) (a z : I) (D : Derivation ℤ R R) :
    ChartDerivation.Construction.blowupChartDerivation I a D (ExceptionalIdeal.Construction.blowupChartRatio I a z) =
      Blowup.Charts.Construction.blowupChartConstants I a (D z.val) -
        Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * ExceptionalIdeal.Construction.blowupChartRatio I a z := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let r := ExceptionalIdeal.Construction.blowupChartRatio I a z
  let δ := ChartDerivation.Construction.blowupChartDerivation I a D
  have h := congrArg δ (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z)
  rw [δ.leibniz, ChartDerivation.Construction.blowupChartDerivation_constants, ChartDerivation.Construction.blowupChartDerivation_constants] at h
  change c * δ r + r * (c * Blowup.Charts.Construction.blowupChartConstants I a (D a.val)) =
    c * Blowup.Charts.Construction.blowupChartConstants I a (D z.val) at h
  apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
  exact quotient_rule_identity c (δ r) (Blowup.Charts.Construction.blowupChartConstants I a (D a.val))
    (Blowup.Charts.Construction.blowupChartConstants I a (D z.val)) r h

/-- A coordinate remains a coordinate after dividing by a denominator
annihilated by its derivation. -/
theorem blowupChartDerivation_coordinate (I : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) :
    ChartDerivation.Construction.blowupChartDerivation I a D (ExceptionalIdeal.Construction.blowupChartRatio I a z) = 1 := by
  rw [blowupChartDerivation_ratio, ha, hz, map_zero, map_one,
    zero_mul (ExceptionalIdeal.Construction.blowupChartRatio I a z), sub_zero (1 : Blowup.Charts.Construction.blowupChart I a)]

/-- When the denominator has derivative zero, differentiating a divided
section simply lowers its exceptional exponent by one. -/
theorem blowupChart_coordinate_derivative_division (I : Ideal R) (a : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (n : ℕ) (p : R) (q : Blowup.Charts.Construction.blowupChart I a)
    (h : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (n + 1) * q) :
    Blowup.Charts.Construction.blowupChartConstants I a (D p) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ n *
      ChartDerivation.Construction.blowupChartDerivation I a D q := by
  simpa only [ha, map_zero, mul_zero ((n + 1 : ℕ) : Blowup.Charts.Construction.blowupChart I a), zero_mul q,
    add_zero (ChartDerivation.Construction.blowupChartDerivation I a D q)] using
    DifferentialBlowupTransform.Construction.blowupChart_derivative_division I a D n p q h

/-- Repeated differentiation lowers the exceptional exponent by the number
of derivatives, without correction terms in these coordinate charts. -/
theorem blowupChart_iteratedCoordinateDerivation_division (I : Ideal R) (a : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (n j : ℕ) (p : R) (q : Blowup.Charts.Construction.blowupChart I a)
    (h : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (n + j) * q) :
    Blowup.Charts.Construction.blowupChartConstants I a (D^[j] p) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ n *
      (ChartDerivation.Construction.blowupChartDerivation I a D)^[j] q := by
  induction j generalizing n with
  | zero => simpa using h
  | succ j ih =>
    have he := ih (n + 1) (by simpa only [Nat.add_assoc, Nat.add_comm 1 j] using h)
    simpa only [Function.iterate_succ_apply'] using
      blowupChart_coordinate_derivative_division I a D ha n (D^[j] p)
        ((ChartDerivation.Construction.blowupChartDerivation I a D)^[j] q) he

variable (I J : Ideal R) (a : I) (b : ℕ) (hJ : J ≤ I ^ b)

/-- The uniquely divided section of the controlled transform. -/
def blowupChartTransformSection (p : J) : Blowup.Charts.Construction.blowupChart I a :=
  Classical.choose (ControlledTransform.Construction.blowup_controlledTransform_unique_division I J b a hJ p).exists

theorem blowupChartTransformSection_spec (p : J) :
    Blowup.Charts.Construction.blowupChartConstants I a p.val = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b *
      blowupChartTransformSection I J a b hJ p :=
  (Classical.choose_spec (ControlledTransform.Construction.blowup_controlledTransform_unique_division I J b a hJ p).exists).symm

/-- The divided original sections generate the actual controlled ideal. -/
theorem blowupControlledTransform_eq_span_divisions :
    ControlledTransform.Construction.blowupControlledTransform I J b a =
      Ideal.span (Set.range (blowupChartTransformSection I J a b hJ)) :=
  PolynomialTransformIdeals.Construction.ideal_colon_eq_span_divisions J (Blowup.Charts.Construction.blowupChartConstants I a) _
    (IsRegular.pow (a := Blowup.Charts.Construction.blowupChartConstants I a a.val) b
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)) _ (blowupChartTransformSection_spec I J a b hJ)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupTransform.Construction
