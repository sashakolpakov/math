import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.QuadraticLower

/-! # Tensor Metric Uniform Lower -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricUniformLower

noncomputable section

/-! The actual full covariant tensor metric uniformly controls its ordinary norm on compact coefficient sets. -/

open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E D ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_parameter_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (N P : D → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set D} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hN : ContDiffOn ℝ ∞ N U) (hP : ContDiffOn ℝ ∞ P U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => CovectorTensorAlgebra.covectorTensorMetricPair b n (B x) (N x) (P x)) U := by
  apply ContDiffOn.sum
  intro i _
  have hS := (Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  exact Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n B _ _ hB (hN.clm_apply hS)
    (hP.clm_apply contDiffOn_const)
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))

theorem covectorTensorMetricPair_uniform_lower (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) {U K : Set D} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n,
      c * ‖N‖ ^ 2 ≤ (CovectorTensorAlgebra.covectorTensorMetricPair b n (B x) N N).re := by
  let T := E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n
  let : FiniteDimensional ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateLinearEquiv b n).symm.finiteDimensional
  let : FiniteDimensional ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := FiniteDimensional.trans ℝ ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
  have hs : ContDiffOn ℝ ∞
      (fun p : D × T => CovectorTensorAlgebra.covectorTensorMetricPair b n (B p.1) p.2 p.2) (U ×ˢ univ) :=
    covectorTensorMetricPair_parameter_smoothOn b n (fun p : D × T => B p.1) Prod.snd Prod.snd
      (hU.prod isOpen_univ) (hB.comp contDiffOn_fst (fun _ hp => hp.1)) contDiffOn_snd contDiffOn_snd
      (fun _ hp => hBs _ hp.1) (fun _ hp => hpos _ hp.1)
  apply Compact.QuadraticLower.positive_quadratic_uniform_lower (fun x N => (CovectorTensorAlgebra.covectorTensorMetricPair b n (B x) N N).re) hK
    ((Complex.continuous_re.comp_continuousOn hs.continuousOn).mono (fun _ hp => ⟨hKU hp.1, hp.2⟩))
  · intro x _
    have hz := TensorMetricRe.covectorTensorMetricPair_re_real_smul_left b n (B x) 0 0 0
    simpa only [zero_smul, zero_mul] using hz
  · intro x _ r N
    rw [TensorMetricRe.covectorTensorMetricPair_re_real_smul_left, TensorMetricRe.covectorTensorMetricPair_re_real_smul_right]
    ring
  · intro x hx N hN
    exact TensorMetricRe.covectorTensorMetricPair_re_pos b n (B x) (hBs x (hKU hx)) (hpos x (hKU hx)) N hN

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricUniformLower
