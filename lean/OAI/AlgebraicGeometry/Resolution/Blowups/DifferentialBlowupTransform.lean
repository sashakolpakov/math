import OAI.AlgebraicGeometry.Resolution.Blowups.ChartDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform

/-! # Differential Blowup Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialBlowupTransform.Construction

noncomputable section

/-! Differential order bounds after arbitrary actual affine chart blowups. -/

universe u

variable {R : Type u} [CommRing R]

theorem ringDerivation_pow_succ (D : Derivation ℤ R R) (r : R) (n : ℕ) :
    D (r ^ (n + 1)) = (n + 1 : ℕ) * r ^ n * D r := by
  rw [D.leibniz_pow]
  simp only [Nat.add_sub_cancel_right, nsmul_eq_mul, smul_eq_mul, mul_assoc]

/-- The derivative of a divided section has an explicit divided-section
formula using the lifted derivation. -/
theorem blowupChart_derivative_division (I : Ideal R) (a : I) (D : Derivation ℤ R R)
    (n : ℕ) (p : R) (q : Blowup.Charts.Construction.blowupChart I a)
    (h : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (n + 1) * q) :
    Blowup.Charts.Construction.blowupChartConstants I a (D p) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ n *
      (ChartDerivation.Construction.blowupChartDerivation I a D q +
        (n + 1 : ℕ) * Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * q) := by
  let δ := ChartDerivation.Construction.blowupChartDerivation I a D
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let d := Blowup.Charts.Construction.blowupChartConstants I a (D a.val)
  have hδc : δ c = c * d := ChartDerivation.Construction.blowupChartDerivation_constants I a D a.val
  have he := congrArg δ h
  rw [ChartDerivation.Construction.blowupChartDerivation_constants, δ.leibniz, ringDerivation_pow_succ δ c n, hδc] at he
  change c * Blowup.Charts.Construction.blowupChartConstants I a (D p) =
    c ^ (n + 1) * δ q + q * ((n + 1 : ℕ) * c ^ n * (c * d)) at he
  apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
  calc
    c * Blowup.Charts.Construction.blowupChartConstants I a (D p) =
        c ^ (n + 1) * δ q + q * ((n + 1 : ℕ) * c ^ n * (c * d)) := he
    _ = c * (c ^ n * (δ q + (n + 1 : ℕ) * d * q)) := by rw [pow_succ c]; ring

/-- One differentiation lowers the order of a divided section by at most one. -/
theorem blowupChart_derivative_preserves_order (I : Ideal R) (a : I) (D : Derivation ℤ R R)
    (n : ℕ) (p : R) (q : Blowup.Charts.Construction.blowupChart I a)
    (h : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (n + 1) * q)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) (hq : q ∈ M ^ (n + 1)) :
    ∃ q' : Blowup.Charts.Construction.blowupChart I a,
      Blowup.Charts.Construction.blowupChartConstants I a (D p) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ n * q' ∧
      q' ∈ M ^ n := by
  refine ⟨ChartDerivation.Construction.blowupChartDerivation I a D q +
    (n + 1 : ℕ) * Blowup.Charts.Construction.blowupChartConstants I a (D a.val) * q,
    blowupChart_derivative_division I a D n p q h, ?_⟩
  apply Ideal.add_mem
  · exact DifferentialOrder.Construction.derivation_mem_pow (ChartDerivation.Construction.blowupChartDerivation I a D) M n hq
  · apply (M ^ n).mul_mem_left
    exact Ideal.pow_le_pow_right (show n ≤ n + 1 by omega) hq

/-- Successively apply a list of ring derivations. -/
def iteratedRingDerivation : List (Derivation ℤ R R) → R → R
  | [], p => p
  | D :: Ds, p => iteratedRingDerivation Ds (D p)

/-- Differential transforms of order `k` remain in the corresponding
power `n` when the original controlled transform has order at least `n+k`. -/
theorem blowupChart_iteratedDerivation_order (I : Ideal R) (a : I)
    (Ds : List (Derivation ℤ R R)) (n : ℕ) (p : R) (q : Blowup.Charts.Construction.blowupChart I a)
    (h : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (n + Ds.length) * q)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) (hq : q ∈ M ^ (n + Ds.length)) :
    ∃ q' : Blowup.Charts.Construction.blowupChart I a,
      Blowup.Charts.Construction.blowupChartConstants I a (Construction.iteratedRingDerivation Ds p) =
        Blowup.Charts.Construction.blowupChartConstants I a a.val ^ n * q' ∧ q' ∈ M ^ n := by
  induction Ds generalizing p q with
  | nil => exact ⟨q, by simpa [Construction.iteratedRingDerivation] using h, by simpa using hq⟩
  | cons D Ds ih =>
    obtain ⟨q', he, hq'⟩ := blowupChart_derivative_preserves_order I a D (n + Ds.length) p q
      (by simpa only [List.length_cons, Nat.add_assoc] using h) M
      (by simpa only [List.length_cons, Nat.add_assoc] using hq)
    exact ih (D p) q' he hq'

/-- The transform of any differential equation of control one vanishes
on the high-order locus of the original transformed ideal. -/
theorem blowupChart_derivative_equation_vanishes (I J : Ideal R) (a : I)
    (Ds : List (Derivation ℤ R R)) (p : J) (hJ : J ≤ I ^ (Ds.length + 1))
    (u : R) (hd : Construction.iteratedRingDerivation Ds p.val = u * a.val)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a))
    (hM : ControlledTransform.Construction.blowupControlledTransform I J (Ds.length + 1) a ≤ M ^ (Ds.length + 1)) :
    Blowup.Charts.Construction.blowupChartConstants I a u ∈ M := by
  obtain ⟨q, hq, _⟩ := ControlledTransform.Construction.blowup_controlledTransform_unique_division I J (Ds.length + 1) a hJ p
  have hqT : q ∈ ControlledTransform.Construction.blowupControlledTransform I J (Ds.length + 1) a := by
    apply Ideal.mem_colon_span_singleton.mpr
    change q * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (Ds.length + 1) ∈
      J.map (Blowup.Charts.Construction.blowupChartConstants I a)
    rw [mul_comm q (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (Ds.length + 1)), hq]
    exact Ideal.mem_map_of_mem _ p.property
  obtain ⟨q', he, hq'⟩ := blowupChart_iteratedDerivation_order I a Ds 1 p.val q
    (by simpa only [Nat.add_comm 1 Ds.length] using hq.symm) M
    (by simpa only [Nat.add_comm 1 Ds.length] using hM hqT)
  rw [hd, map_mul, pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val),
    mul_comm (Blowup.Charts.Construction.blowupChartConstants I a u) (Blowup.Charts.Construction.blowupChartConstants I a a.val)] at he
  have he' : Blowup.Charts.Construction.blowupChartConstants I a u = q' :=
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left he
  simpa only [pow_one, ← he'] using hq'

/-- For any chart denominator, the strict-transform equation of a
control-one derivative vanishes on the transformed high-order locus. -/
theorem blowupChart_derivative_ratio_vanishes (I J : Ideal R) (a z : I)
    (Ds : List (Derivation ℤ R R)) (p : J) (hJ : J ≤ I ^ (Ds.length + 1))
    (hd : Construction.iteratedRingDerivation Ds p.val = z.val)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a))
    (hM : ControlledTransform.Construction.blowupControlledTransform I J (Ds.length + 1) a ≤ M ^ (Ds.length + 1)) :
    ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M := by
  obtain ⟨q, hq, _⟩ := ControlledTransform.Construction.blowup_controlledTransform_unique_division I J (Ds.length + 1) a hJ p
  have hqT : q ∈ ControlledTransform.Construction.blowupControlledTransform I J (Ds.length + 1) a := by
    apply Ideal.mem_colon_span_singleton.mpr
    change q * Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (Ds.length + 1) ∈
      J.map (Blowup.Charts.Construction.blowupChartConstants I a)
    rw [mul_comm q (Blowup.Charts.Construction.blowupChartConstants I a a.val ^ (Ds.length + 1)), hq]
    exact Ideal.mem_map_of_mem _ p.property
  obtain ⟨q', he, hq'⟩ := blowupChart_iteratedDerivation_order I a Ds 1 p.val q
    (by simpa only [Nat.add_comm 1 Ds.length] using hq.symm) M
    (by simpa only [Nat.add_comm 1 Ds.length] using hM hqT)
  rw [hd, pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val), ← ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z] at he
  have he' : ExceptionalIdeal.Construction.blowupChartRatio I a z = q' :=
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left he
  simpa only [pow_one, ← he'] using hq'

/-- A chart whose denominator is a unit multiple of a control-one
derivative equation contains no proper ideal of the transformed high-order locus. -/
theorem blowupChart_no_highOrder_of_unit_derivative (I J : Ideal R) (a : I)
    (Ds : List (Derivation ℤ R R)) (p : J) (hJ : J ≤ I ^ (Ds.length + 1))
    (u : R) (hu : IsUnit u) (hd : Construction.iteratedRingDerivation Ds p.val = u * a.val)
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a))
    (hM : ControlledTransform.Construction.blowupControlledTransform I J (Ds.length + 1) a ≤ M ^ (Ds.length + 1)) : M = ⊤ :=
  M.eq_top_of_isUnit_mem
    (blowupChart_derivative_equation_vanishes I J a Ds p hJ u hd M hM)
    (hu.map (Blowup.Charts.Construction.blowupChartConstants I a))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialBlowupTransform.Construction
