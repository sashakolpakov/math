import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RealPairSymmetry
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergySupport

/-! # Supported Pair Symmetry -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.SupportedPairSymmetry

noncomputable section

/-! Real symmetry of the actual line pairings holds globally when one field is supported in the genuine positive metric chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineMetricTestPair_re_symm_of_support (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E}
    (hc : tsupport c ⊆ U) (hB : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hw : ∀ x ∈ U, w x = Complex.ofReal (w x).re) (x : E) :
    (TensorMetricTest.lineMetricTestPair b n B w a c x).re = (TensorMetricTest.lineMetricTestPair b n B w c a x).re := by
  by_cases hx : x ∈ U
  · exact RealPairSymmetry.lineMetricTestPair_re_symm b n B w a c x (hB x hx) (hpos x hx) (hw x hx)
  · have hzero : c x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hc ht))
    simp only [TensorMetricTest.lineMetricTestPair, hzero, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero,
      inner_zero_left, inner_zero_right, mul_zero, Complex.zero_re]

theorem lineCovectorFullEnergyPair_re_symm_of_support (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (ha : tsupport a ⊆ U)
    (hB : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hw : ∀ x ∈ U, w x = Complex.ofReal (w x).re) (x : E) :
    (RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x).re =
      (RoughDivergence.lineCovectorFullEnergyPair b n B G A w c a x).re := by
  by_cases hx : x ∈ U
  · exact RealPairSymmetry.lineCovectorFullEnergyPair_re_symm b n B G A w a c x (hB x hx) (hpos x hx) (hw x hx)
  · have hnot : x ∉ tsupport a := fun ht => hx (ha ht)
    rw [EnergySupport.lineCovectorFullEnergyPair_zero_left b n B G A w a c x hnot,
      EnergySupport.lineCovectorFullEnergyPair_zero_right b n B G A w c a x hnot]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.SupportedPairSymmetry
