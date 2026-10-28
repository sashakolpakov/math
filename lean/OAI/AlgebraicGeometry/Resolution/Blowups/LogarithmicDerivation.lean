import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupTransform

/-! # Logarithmic Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicDerivation.Construction

noncomputable section

/-! Derivations tangent to a boundary and their actual lifts to blowup charts. -/

variable {R ι : Type*} [CommRing R]

/-- Logarithmic derivations preserve each principal boundary equation's ideal. -/
def logarithmicDerivations (w : ι → R) : Submodule R (Derivation ℤ R R) where
  carrier := {D | ∀ i, D (w i) ∈ Ideal.span {w i}}
  zero_mem' i := by simp
  add_mem' hD hE i := by
    change _ + _ ∈ Ideal.span {w i}
    exact (Ideal.span {w i}).add_mem (hD i) (hE i)
  smul_mem' r D hD i := by
    change r • D (w i) ∈ Ideal.span {w i}
    exact (Ideal.span {w i}).smul_mem r (hD i)

/-- Every lifted derivation is tangent to the new exceptional equation. -/
theorem blowupChartDerivation_tangent_exceptional (I : Ideal R) (a : I) (D : Derivation ℤ R R) :
    ChartDerivation.Construction.blowupChartDerivation I a D (Blowup.Charts.Construction.blowupChartConstants I a a.val) ∈
      Ideal.span {Blowup.Charts.Construction.blowupChartConstants I a a.val} := by
  rw [ChartDerivation.Construction.blowupChartDerivation_constants]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- Tangency survives division of a boundary equation by any exceptional
power whenever that division holds on the actual Rees chart. -/
theorem blowupChartDerivation_tangent_divided_boundary
    (I : Ideal R) (a : I) (D : Derivation ℤ R R) (p : R)
    (hDp : D p ∈ Ideal.span {p}) (q : Blowup.Charts.Construction.blowupChart I a) (e : ℕ)
    (he : Blowup.Charts.Construction.blowupChartConstants I a p = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e * q) :
    ChartDerivation.Construction.blowupChartDerivation I a D q ∈ Ideal.span {q} := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let φ := Blowup.Charts.Construction.blowupChartConstants I a
  let δ := ChartDerivation.Construction.blowupChartDerivation I a D
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hDp
  cases e with
  | zero =>
    have hq : φ p = q := by
      simpa only [pow_zero (Blowup.Charts.Construction.blowupChartConstants I a a.val), one_mul q] using he
    rw [← hq, ChartDerivation.Construction.blowupChartDerivation_constants, ht, map_mul]
    exact (Ideal.span {φ p}).mul_mem_left c
      ((Ideal.span {φ p}).mul_mem_right (φ t) (Ideal.mem_span_singleton_self (φ p)))
  | succ n =>
    have hdiv := DifferentialBlowupTransform.Construction.blowupChart_derivative_division I a D n p q he
    have hEq : δ q + (n + 1 : ℕ) * φ (D a.val) * q = c * q * φ t := by
      apply (IsRegular.pow (a := c) n (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)).left
      change c ^ n * (δ q + (n + 1 : ℕ) * φ (D a.val) * q) = c ^ n * (c * q * φ t)
      calc
        _ = φ (D p) := hdiv.symm
        _ = _ := by
          rw [ht, map_mul, he, pow_succ c]
          ring
    have hleft : c * q * φ t ∈ Ideal.span {q} :=
      (Ideal.span {q}).mul_mem_right (φ t)
        ((Ideal.span {q}).mul_mem_left c (Ideal.mem_span_singleton_self q))
    have hright : (n + 1 : ℕ) * φ (D a.val) * q ∈ Ideal.span {q} :=
      (Ideal.span {q}).mul_mem_left _ (Ideal.mem_span_singleton_self q)
    have hsub := (Ideal.span {q}).sub_mem hleft hright
    rw [← hEq, add_sub_cancel_right (δ q)
      (((n + 1 : ℕ) : Blowup.Charts.Construction.blowupChart I a) * φ (D a.val) * q)] at hsub
    exact hsub

/-- Lifted logarithmic derivations preserve all divided old boundary
equations and the new exceptional equation simultaneously. -/
theorem blowupChartDerivation_logarithmic
    (I : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (D : logarithmicDerivations w) :
    ChartDerivation.Construction.blowupChartDerivation I a D.val ∈ logarithmicDerivations
      (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w') := by
  intro i
  cases i with
  | none => exact blowupChartDerivation_tangent_exceptional I a D.val
  | some i =>
    exact blowupChartDerivation_tangent_divided_boundary I a D.val
      (w i) (D.property i) (w' i) (e i) (he i)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicDerivation.Construction
