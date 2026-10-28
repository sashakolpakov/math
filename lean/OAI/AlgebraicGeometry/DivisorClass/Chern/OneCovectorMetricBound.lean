import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricSharp
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm

/-! # One Covector Metric Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricBound

noncomputable section

section

/-! Pointwise control of actual one-covectors by the original positive tangent metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
theorem positiveMetric_cauchy_schwarz (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (v w : E) :
    B v w * B v w ≤ B v v * B w w := by
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  exact real_inner_mul_inner_self_le (L.symm v) (L.symm w)

theorem oneCovectorMetric_real_duals (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
    let s := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re = B r r + B s s := by
  rw [OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos]
  dsimp only
  rw [Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos, Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos]
  rfl

theorem oneCovectorMetric_eval_sq_le (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : E) :
    ‖AntiOneFormCoordinates.oneFormLinear a v‖ ^ 2 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re * B v v := by
  let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
  let s := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
  have hr := positiveMetric_cauchy_schwarz B hB hpos r v
  have hi := positiveMetric_cauchy_schwarz B hB hpos s v
  have hre : B r v = (AntiOneFormCoordinates.oneFormLinear a v).re := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos _ v
  have him : B s v = (AntiOneFormCoordinates.oneFormLinear a v).im := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos _ v
  have hp := oneCovectorMetric_real_duals b B hB hpos a
  change (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re = B r r + B s s at hp
  rw [hre] at hr
  rw [him] at hi
  rw [Complex.sq_norm, Complex.normSq_apply, hp]
  nlinarith

theorem oneCovectorMetric_norm_sq_le (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    ‖a‖ ^ 2 ≤ ‖B‖ * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  let P := (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re
  have hP : 0 ≤ P := by
    dsimp only [P]
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b 1 B hB hpos]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg 1 _
  have hsqrt := Real.sq_sqrt (mul_nonneg (norm_nonneg B) hP)
  have hnorm : ‖AntiOneFormCoordinates.oneFormLinear a‖ ≤ Real.sqrt (‖B‖ * P) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hv : B v v ≤ ‖B‖ * ‖v‖ * ‖v‖ := by
      calc
        _ ≤ ‖B v v‖ := le_abs_self _
        _ ≤ ‖B v‖ * ‖v‖ := (B v).le_opNorm v
        _ ≤ _ := mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg v)
    have hsq : ‖AntiOneFormCoordinates.oneFormLinear a v‖ ^ 2 ≤ (Real.sqrt (‖B‖ * P) * ‖v‖) ^ 2 := by
      calc
        _ ≤ P * (‖B‖ * ‖v‖ * ‖v‖) :=
          (oneCovectorMetric_eval_sq_le b B hB hpos a v).trans (mul_le_mul_of_nonneg_left hv hP)
        _ = _ := by rw [mul_pow, hsqrt]; ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp hsq
  rw [OneCovectorProjectionNorm.oneFormLinear_norm] at hnorm
  have h := (sq_le_sq₀ (norm_nonneg a) (Real.sqrt_nonneg (‖B‖ * P))).mpr hnorm
  rw [hsqrt] at h
  exact h

end

/-! An explicit upper bound for the original one-covector metric pairing using its actual inverse metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Components
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexCovector_re_norm_le (q : E →L[ℝ] ℂ) : ‖Complex.reCLM.comp q‖ ≤ ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q)
  intro v
  change |(q v).re| ≤ ‖q‖ * ‖v‖
  exact (Complex.abs_re_le_norm (q v)).trans (q.le_opNorm v)

theorem complexCovector_im_norm_le (q : E →L[ℝ] ℂ) : ‖Complex.imCLM.comp q‖ ≤ ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg q)
  intro v
  change |(q v).im| ≤ ‖q‖ * ‖v‖
  exact (Complex.abs_im_le_norm (q v)).trans (q.le_opNorm v)

end Components

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem oneCovectorMetric_pair_abs_le (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    |(Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a c).re| ≤ 2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖a‖ * ‖c‖ := by
  let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear c))
  let s := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear c))
  have hrc := complexCovector_re_norm_le (AntiOneFormCoordinates.oneFormLinear c)
  have hic := complexCovector_im_norm_le (AntiOneFormCoordinates.oneFormLinear c)
  rw [OneCovectorProjectionNorm.oneFormLinear_norm] at hrc hic
  have hr : ‖r‖ ≤ ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖c‖ :=
    ((Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B).le_opNorm _).trans (mul_le_mul_of_nonneg_left hrc (norm_nonneg _))
  have hs : ‖s‖ ≤ ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖c‖ :=
    ((Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B).le_opNorm _).trans (mul_le_mul_of_nonneg_left hic (norm_nonneg _))
  have ha1 := (AntiOneFormCoordinates.oneFormLinear a).le_opNorm r
  have ha2 := (AntiOneFormCoordinates.oneFormLinear a).le_opNorm s
  rw [OneCovectorProjectionNorm.oneFormLinear_norm] at ha1 ha2
  rw [OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos]
  change |(AntiOneFormCoordinates.oneFormLinear a r).re + (AntiOneFormCoordinates.oneFormLinear a s).im| ≤ _
  calc
    _ ≤ |(AntiOneFormCoordinates.oneFormLinear a r).re| + |(AntiOneFormCoordinates.oneFormLinear a s).im| := abs_add_le _ _
    _ ≤ ‖AntiOneFormCoordinates.oneFormLinear a r‖ + ‖AntiOneFormCoordinates.oneFormLinear a s‖ :=
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
    _ ≤ ‖a‖ * ‖r‖ + ‖a‖ * ‖s‖ := add_le_add ha1 ha2
    _ ≤ ‖a‖ * (‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖c‖) + ‖a‖ * (‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖c‖) := by gcongr
    _ = _ := by ring

theorem oneCovectorMetric_pair_control (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (C : ℝ) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C * ‖a‖) :
    |(Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B c a).re| ≤
      (2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * C * ‖B‖) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re := by
  calc
    _ ≤ 2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * ‖c‖ * ‖a‖ := oneCovectorMetric_pair_abs_le b B hB hpos c a
    _ ≤ 2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * (C * ‖a‖) * ‖a‖ := by gcongr
    _ = (2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * C) * ‖a‖ ^ 2 := by ring
    _ ≤ (2 * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B‖ * C) * (‖B‖ * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re) :=
      mul_le_mul_of_nonneg_left (oneCovectorMetric_norm_sq_le b B hB hpos a) (by positivity)
    _ = _ := by ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorMetricBound
