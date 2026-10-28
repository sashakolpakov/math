import OAI.AlgebraicGeometry.Picard.ThetaConstruction.InfinitesimalGauge
import OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity

/-! # Gauge Normalization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! A holomorphic dual-number gauge has constant scalar reduction.
Its nonzero value at the origin gives the actual normalized gauge. -/

section

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} (T : DefinitionsIntegral.MarkedPolarizedTorus dim E)

theorem DefinitionsIntegral.MarkedPolarizedTorus.dualNumberGauge_reduction_constant (a : DefinitionsIntegral.Tangent dim)
    (c : DefinitionsIntegral.Tangent dim → DualNumber ℂ)
    (hc : Differentiable ℂ (fun w => (c w).fst))
    (htrans : ∀ (l : T.lattice) w, c (w + l.val) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * T.riemannForm l.val a)) = c w)
    (v w : DefinitionsIntegral.Tangent dim) : (c v).fst = (c w).fst := by
  let : CompactSpace ((DefinitionsIntegral.Tangent dim) ⧸ T.lattice) := T.compact
  apply RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity.normPeriodic_holomorphic_constant T.lattice (fun t => (c t).fst) _ hc v w
  intro l t
  have H := congrArg TrivSqZeroExt.fst (htrans l t)
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_one,
    TrivSqZeroExt.fst_inr, add_zero, mul_one] at H
  exact congrArg norm H

theorem DefinitionsIntegral.MarkedPolarizedTorus.dualNumberGauge_nonzero_reduction_eq_zero (a : DefinitionsIntegral.Tangent dim)
    (c : DefinitionsIntegral.Tangent dim → DualNumber ℂ)
    (hc : ∀ w, RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt c w) (hzero : (c 0).fst ≠ 0)
    (htrans : ∀ (l : T.lattice) w, c (w + l.val) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * T.riemannForm l.val a)) = c w) : a = 0 := by
  let d : DualNumber ℂ := TrivSqZeroExt.inl ((c 0).fst)⁻¹
  let c' := fun w => d * c w
  have hfirst (w : DefinitionsIntegral.Tangent dim) : (c' w).fst = 1 := by
    change (c 0).fst⁻¹ * (c w).fst = 1
    rw [T.dualNumberGauge_reduction_constant a c (fun t => (hc t).1) htrans w 0]
    exact inv_mul_cancel₀ hzero
  have hdiff : Differentiable ℂ (fun w => (c' w).snd) := fun w =>
    (RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.dualCoefficientDifferentiableAt_mul (fun _ => d) c w
      ⟨differentiableAt_const _, differentiableAt_const _⟩ (hc w)).2
  apply T.dualNumberGauge_eq_zero a c' hdiff hfirst
  intro l w
  change (d * c (w + l.val)) * _ = d * c w
  rw [mul_assoc, htrans]

end

namespace GaugeNormalization.Geometric.MarkedPolarizedTorus

end GaugeNormalization.Geometric.MarkedPolarizedTorus

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
