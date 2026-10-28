import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence

/-! # Energy Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergySupport

noncomputable section

/-! The full covariant energy pairing is supported inside the support of either of its original smooth coefficient fields. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] [Fintype ι] [LinearOrder ι] in
theorem lineCovectorConnectionDerivative_zero_off_support (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (hx : x ∉ tsupport a) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a x = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  exact image_eq_zero_of_notMem_tsupport (f := fun y => ConnectionSymbols.lineCovectorConnectionDerivative n G A a y v)
    (fun ht => hx (CovectorConnectionSupport.lineCovectorConnectionDerivative_column_tsupport n G A a v ht))

theorem lineCovectorFullEnergyPair_zero_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (hc : x ∉ tsupport c) :
    RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x = 0 := by
  have hzero := lineCovectorConnectionDerivative_zero_off_support n G A c x hc
  simp only [RoughDivergence.lineCovectorFullEnergyPair, hzero, CovectorTensorAlgebra.covectorTensorMetricPair, _root_.zero_apply,
    Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, Finset.sum_const_zero, mul_zero]

theorem lineCovectorFullEnergyPair_zero_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (ha : x ∉ tsupport a) :
    RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x = 0 := by
  have hzero := lineCovectorConnectionDerivative_zero_off_support n G A a x ha
  simp only [RoughDivergence.lineCovectorFullEnergyPair, hzero, CovectorTensorAlgebra.covectorTensorMetricPair, _root_.zero_apply,
    Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_left, Finset.sum_const_zero, mul_zero]

theorem lineCovectorFullEnergyPair_tsupport_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    tsupport (RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c) ⊆ tsupport c := by
  apply closure_minimal _ (isClosed_tsupport c)
  intro x hx
  by_contra h
  exact hx (lineCovectorFullEnergyPair_zero_right b n B G A w a c x h)

theorem lineCovectorFullEnergyPair_tsupport_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    tsupport (RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra h
  exact hx (lineCovectorFullEnergyPair_zero_left b n B G A w a c x h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergySupport
