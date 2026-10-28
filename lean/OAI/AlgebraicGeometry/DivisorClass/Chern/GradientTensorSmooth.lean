import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricUniformLower

/-! # Gradient Tensor Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorSmooth

noncomputable section

/-! Smoothness and a genuine uniform ellipticity bound for the explicit tensor coefficient on compact chart sets. -/

open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E D ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

theorem covectorGradientCoefficient_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (r : D → ℝ) {U : Set D} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hr : ContDiffOn ℝ ∞ r U)
    (hBs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => GradientTensorCoefficient.covectorGradientCoefficient b n (B x) (r x)) U := by
  have hM : ContDiffOn ℝ ∞ (fun x => Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x))⁻¹) U :=
    Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator_smoothOn _ (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.matrixInverse_entry_smoothOn
      (fun x => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)) (Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearExteriorGram_entry_smooth b n B hB)
      (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx)))
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  unfold GradientTensorCoefficient.covectorGradientCoefficient
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  have hc : ContDiffOn ℝ ∞ (fun x => b.repr (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) j) U :=
    (b.coord j).toContinuousLinearMap.contDiff.comp_contDiffOn (hS.clm_apply contDiffOn_const)
  exact (hr.mul hc).smul (contDiffOn_const.clm_comp (hM.clm_comp contDiffOn_const))

theorem covectorGradientCoefficient_uniform_lower (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (r : D → ℝ) {U K : Set D} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hr : ContDiffOn ℝ ∞ r U)
    (hBs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hrp : ∀ x ∈ U, 0 < r x) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : GradientTensorCoordinates.CovectorGradientCoordinates ι n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (GradientTensorCoefficient.covectorGradientCoefficient b n (B x) (r x) v) v := by
  let F := GradientTensorCoordinates.CovectorGradientCoordinates ι n
  let Q := fun x (v : F) => inner ℝ (GradientTensorCoefficient.covectorGradientCoefficient b n (B x) (r x) v) v
  have hA := covectorGradientCoefficient_smoothOn b n B r hU hB hr hBs hpos
  have hAc : ContinuousOn (fun p : D × F => GradientTensorCoefficient.covectorGradientCoefficient b n (B p.1) (r p.1) p.2) (K ×ˢ univ) :=
    (((hA.continuousOn.mono hKU).comp continuousOn_fst (fun _ hp => hp.1)).clm_apply continuousOn_snd)
  apply Compact.QuadraticLower.positive_quadratic_uniform_lower Q hK (hAc.inner continuousOn_snd)
  · intro x _
    simp only [Q, map_zero, inner_zero_left]
  · intro x _ t v
    dsimp only [Q]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  · intro x hx v hv
    exact GradientTensorCoefficient.covectorGradientCoefficient_positive b n (B x) (hBs x (hKU hx)) (hpos x (hKU hx))
      (r x) (hrp x (hKU hx)) v hv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorSmooth
