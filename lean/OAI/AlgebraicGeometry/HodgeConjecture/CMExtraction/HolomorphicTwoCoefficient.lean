import OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoCoefficient

/-! # Holomorphic Two Coefficient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicTwoCoefficient.Closedness

noncomputable section

/-! The genuine (2,0) component of a real alternating two-form. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type20_J (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f)
    (u v : E) :
    ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) (Complex.I • v) = -ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  have h := hf Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit ![u, v]
  have hc : Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 2 0 Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit = -1 := by
    simp [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Analysis.HodgeTheory.Decomposition.KahlerMetric.Constructions.metricIUnit]
  rw [hc, neg_one_mul] at h
  rw [ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply, ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type20_J_balance (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) (u v : E) :
    ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v = ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v) := by
  have h := twoFormBilinear_type20_J f hf u (Complex.I • v)
  rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  exact neg_injective h

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type20_J_left (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) (u v : E) :
    ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v = Complex.I * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  have hn : (1 + Complex.I : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have h := hf (Units.mk0 (1 + Complex.I) hn) ![u, v]
  have hv : (fun i => ((Units.mk0 (1 + Complex.I) hn : ℂˣ) : ℂ) • ![u, v] i) =
      ![u + Complex.I • u, v + Complex.I • v] := by
    ext i
    fin_cases i <;> simp [add_smul]
  rw [hv, ← ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply, ← ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear_apply] at h
  simp only [map_add, add_apply, twoFormBilinear_type20_J f hf,
    ← twoFormBilinear_type20_J_balance f hf, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Units.val_mk0,
    pow_zero, mul_one] at h
  linear_combination (norm := ring_nf) h / 2
  rw [Complex.I_sq]
  ring

omit [IsScalarTower ℝ ℂ E] in
theorem twoFormBilinear_type20_J_right (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) (u v : E) :
    ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v) = Complex.I * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  rw [← twoFormBilinear_type20_J_balance f hf, twoFormBilinear_type20_J_left f hf]

def holomorphicTwoCoefficient (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) : ℂ :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E (E →L[ℝ] ℂ) (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f) u) v

theorem holomorphicTwoCoefficient_apply (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    holomorphicTwoCoefficient f u v = (1 / 4 : ℂ) *
      (ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u v - ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) (Complex.I • v) -
        Complex.I * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v) -
        Complex.I * ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v) := by
  simp only [holomorphicTwoCoefficient, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply,
    smul_apply, sub_apply, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicTwoCoefficient_type20 (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 f) (u v : E) :
    holomorphicTwoCoefficient f u v = ComplexMultiplication.HodgeComparison.KahlerDifferential.CM.Construction.twoFormBilinear f u v := by
  rw [holomorphicTwoCoefficient_apply, twoFormBilinear_type20_J f hf,
    twoFormBilinear_type20_J_left f hf, twoFormBilinear_type20_J_right f hf]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicTwoCoefficient_skew (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) :
    holomorphicTwoCoefficient f v u = -holomorphicTwoCoefficient f u v := by
  rw [holomorphicTwoCoefficient_apply, holomorphicTwoCoefficient_apply,
    ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f u v, ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f (Complex.I • u) (Complex.I • v),
    ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f (Complex.I • u) v, ComplexMultiplication.HodgeComparison.MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f u (Complex.I • v)]
  ring

def holomorphicTwoBilinear (f : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := holomorphicTwoCoefficient f u
      map_add' := fun v w => by simp only [holomorphicTwoCoefficient, map_add]
      map_smul' := fun z v => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ _ z v }
  map_add' u v := by
    ext w
    change holomorphicTwoCoefficient f (u + v) w =
      holomorphicTwoCoefficient f u w + holomorphicTwoCoefficient f v w
    simp only [holomorphicTwoCoefficient, map_add, add_apply]
  map_smul' z u := by
    ext v
    change holomorphicTwoCoefficient f (z • u) v = z * holomorphicTwoCoefficient f u v
    simp only [holomorphicTwoCoefficient, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul, map_smul,
      smul_apply, smul_eq_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicTwoCoefficient.Closedness
