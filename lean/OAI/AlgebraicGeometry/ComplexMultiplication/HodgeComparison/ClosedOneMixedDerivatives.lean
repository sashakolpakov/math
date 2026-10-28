import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicCodifferential

/-! # Closed One Mixed Derivatives -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction

noncomputable section

/-! Closedness of a genuine one-form equates the mixed derivatives of
its holomorphic and antiholomorphic coefficient projections. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closed_oneForm_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (hclosed : extDeriv f x = 0) (u v : E) :
    fderiv ℝ (fun y => f y (fun _ => v)) x u =
      fderiv ℝ (fun y => f y (fun _ => u)) x v := by
  have h := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2 => a ![u, v]) hclosed
  rw [extDeriv_apply hf, Fin.sum_univ_two] at h
  have h0 : (0 : Fin 2).removeNth ![u, v] = fun _ => v := by ext i; fin_cases i; rfl
  have h1 : (1 : Fin 2).removeNth ![u, v] = fun _ => u := by ext i; fin_cases i; rfl
  rw [h0, h1] at h
  change (1 : ℤ) • fderiv ℝ (fun y => f y (fun _ => v)) x u +
    (-1 : ℤ) • fderiv ℝ (fun y => f y (fun _ => u)) x v = 0 at h
  simpa only [one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem holomorphic_projection_coefficient_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v : E) :
    fderiv ℝ (fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u =
      (1 / 2 : ℂ) * (fderiv ℝ (fun y => f y (fun _ => v)) x u -
        Complex.I * fderiv ℝ (fun y => f y (fun _ => Complex.I • v)) x u) := by
  have hv := (hf.continuousAlternatingMap_apply_const (fun _ => v)).hasFDerivAt
  have hJ := (hf.continuousAlternatingMap_apply_const (fun _ => Complex.I • v)).hasFDerivAt
  have hd := (hv.sub (hJ.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have heq := congrArg (fun L : E →L[ℝ] ℂ => L u) hd.fderiv
  change fderiv ℝ (fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u = _ at heq
  simpa only [smul_apply, sub_apply, smul_eq_mul] using heq

theorem antiholomorphic_projection_coefficient_derivative (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (u v : E) :
    fderiv ℝ (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u =
      (1 / 2 : ℂ) * (fderiv ℝ (fun y => f y (fun _ => v)) x u +
        Complex.I * fderiv ℝ (fun y => f y (fun _ => Complex.I • v)) x u) := by
  have hv := (hf.continuousAlternatingMap_apply_const (fun _ => v)).hasFDerivAt
  have hJ := (hf.continuousAlternatingMap_apply_const (fun _ => Complex.I • v)).hasFDerivAt
  have hd := (hv.add (hJ.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  have heq := congrArg (fun L : E →L[ℝ] ℂ => L u) hd.fderiv
  change fderiv ℝ (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u = _ at heq
  simpa only [smul_apply, add_apply, smul_eq_mul] using heq

theorem closed_oneForm_mixed_derivatives (f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (hf : DifferentiableAt ℝ f x) (hclosed : extDeriv f x = 0) (u v : E) :
    AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative
      (fun y => ComplexCovector.CM.Construction.holomorphicCovectorProjection (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) v) x u =
    MetricDerivative.CM.Construction.holomorphicDirectionalDerivative
      (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (HolomorphicMixedChartPair.CM.Construction.oneCovectorCLM (f y)) u) x v := by
  rw [AntiholomorphicDivergence.CM.Construction.antiholomorphicDirectionalDerivative, MetricDerivative.CM.Construction.holomorphicDirectionalDerivative,
    holomorphic_projection_coefficient_derivative f hf,
    holomorphic_projection_coefficient_derivative f hf,
    antiholomorphic_projection_coefficient_derivative f hf,
    antiholomorphic_projection_coefficient_derivative f hf]
  rw [closed_oneForm_derivative f hf hclosed u v,
    closed_oneForm_derivative f hf hclosed u (Complex.I • v),
    closed_oneForm_derivative f hf hclosed (Complex.I • u) v,
    closed_oneForm_derivative f hf hclosed (Complex.I • u) (Complex.I • v)]
  ring_nf

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneMixedDerivatives.CM.Construction
