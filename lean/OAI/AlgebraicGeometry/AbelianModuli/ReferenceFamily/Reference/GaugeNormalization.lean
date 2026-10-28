import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.InfinitesimalGauge
import OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity

/-! # Gauge Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! A holomorphic infinitesimal gauge has constant reduction. Its unit
value at the origin supplies normalization without an extra choice. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

theorem Fiber.ReferenceAnalyticFiber.dualNumberGauge_reduction_constant (a : Fiber.ReferenceTangent s)
    (c : Fiber.ReferenceTangent s → DualNumber ℂ)
    (hc : Differentiable ℂ (fun w => (c w).fst))
    (htrans : ∀ (l : P.lattice) w, c (w + F.latticeEmbedding l) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a)) = c w)
    (v w : Fiber.ReferenceTangent s) : (c v).fst = (c w).fst := by
  let : CompactSpace (Fiber.ReferenceTangent s ⧸ F.lattice) := F.compact
  apply RepresentationTheory.Theta.Geometric.UnitaryAutomorphyRigidity.normPeriodic_holomorphic_constant F.lattice (fun t => (c t).fst) _ hc v w
  intro l t
  have H := congrArg TrivSqZeroExt.fst (htrans (F.integralLatticeEquiv.symm l) t)
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_one,
    TrivSqZeroExt.fst_inr, add_zero, mul_one] at H
  have hl := F.latticeEmbedding_symm l
  rw [hl] at H
  exact congrArg norm H

theorem Fiber.ReferenceAnalyticFiber.dualNumberGauge_nonzero_reduction_eq_zero (a : Fiber.ReferenceTangent s)
    (c : Fiber.ReferenceTangent s → DualNumber ℂ)
    (hc : ∀ w, RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.DualCoefficientDifferentiableAt c w) (hzero : (c 0).fst ≠ 0)
    (htrans : ∀ (l : P.lattice) w, c (w + F.latticeEmbedding l) *
      (1 + TrivSqZeroExt.inr ((Real.pi : ℂ) * F.form (F.latticeEmbedding l) a)) = c w) : a = 0 := by
  let d : DualNumber ℂ := TrivSqZeroExt.inl ((c 0).fst)⁻¹
  let c' := fun w => d * c w
  have hfirst (w : Fiber.ReferenceTangent s) : (c' w).fst = 1 := by
    change (c 0).fst⁻¹ * (c w).fst = 1
    rw [F.dualNumberGauge_reduction_constant a c (fun t => (hc t).1) htrans w 0]
    exact inv_mul_cancel₀ hzero
  have hdiff : Differentiable ℂ (fun w => (c' w).snd) := fun w =>
    (RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic.dualCoefficientDifferentiableAt_mul (fun _ => d) c w
      ⟨differentiableAt_const _, differentiableAt_const _⟩ (hc w)).2
  apply F.dualNumberGauge_eq_zero a c' hdiff hfirst
  intro l w
  change (d * c (w + F.latticeEmbedding l)) * _ = d * c w
  rw [mul_assoc, htrans]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
