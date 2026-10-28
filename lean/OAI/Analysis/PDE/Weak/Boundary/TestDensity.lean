import OAI.Analysis.PDE.Weak.Boundary.TestSmoothing
import OAI.Analysis.PDE.Green.LocalExtension

/-! A compactly supported C¹ test can be used in a distributional identity
initially known only for smooth compactly supported tests. -/

noncomputable section
open Set Filter _root_.MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_compact_test_cutoff {Ω K : Set X} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ η : X → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω ∧
      ∀ x ∈ K, η x = 1 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : X)
  let U := Ω ∩ Metric.ball (0 : X) R
  have hU : IsOpen U := hΩ.inter Metric.isOpen_ball
  have hKU : K ⊆ U := fun x hx => ⟨hKΩ hx, hKR hx⟩
  obtain ⟨η, hη, _, hone, hzero⟩ :=
    OAI.Analysis.PDE.Green.exists_smooth_cutoff_near_compact hK hU hKU (k := ⊤)
  have hsU : tsupport η ⊆ U := by
    intro x hx
    by_contra hnot
    exact ((notMem_tsupport_iff_eventuallyEq).2 (hzero x hnot)) hx
  refine ⟨η, hη, ?_, fun x hx => (hsU hx).1, fun x hx => (hone x hx).self_of_nhds⟩
  exact (isCompact_closedBall (0 : X) R).of_isClosed_subset (isClosed_tsupport η)
    (fun x hx => Metric.ball_subset_closedBall (hsU hx).2)

variable (μ : Measure X) [μ.IsAddHaarMeasure]

theorem smooth_test_identity_extends_c1
    {Ω : Set X} (hΩ : IsOpen Ω) (u g : X → ℝ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) (w : X)
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, g x * φ x ∂μ) = -(∫ x, u x * fderiv ℝ φ x w ∂μ))
    (φ : X → ℝ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hsΩ : tsupport φ ⊆ Ω) :
    (∫ x, g x * φ x ∂μ) = -(∫ x, u x * fderiv ℝ φ x w ∂μ) := by
  obtain ⟨η, hη, hsη, hηΩ, hone⟩ := exists_compact_test_cutoff hΩ hs.isCompact hsΩ
  have hηφ : (fun x => η x * φ x) = φ := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hone x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  let ψ : ℕ → X → ℝ := fun n x => η x * smoothTestApprox μ φ n x
  have hψ (n : ℕ) : ContDiff ℝ ∞ (ψ n) :=
    hη.mul (smoothTestApprox_contDiff μ hφ.continuous n)
  have hsψ (n : ℕ) : HasCompactSupport (ψ n) := hsη.mul_right
  have hψΩ (n : ℕ) : tsupport (ψ n) ⊆ Ω :=
    (tsupport_mul_subset_left).trans hηΩ
  have hψt (x : X) : Tendsto (fun n => ψ n x) atTop (𝓝 (φ x)) := by
    have h := (tendsto_const_nhds (x := η x)).mul (smoothTestApprox_tendsto μ hφ.continuous x)
    have he : η x * φ x = φ x := congrFun hηφ x
    simpa only [ψ, he] using h
  have hDψ (n : ℕ) (x : X) : fderiv ℝ (ψ n) x w =
      η x * fderiv ℝ (smoothTestApprox μ φ n) x w +
        fderiv ℝ η x w * smoothTestApprox μ φ n x := by
    have h := ((hη.differentiable (by simp) x).hasFDerivAt.mul
      ((smoothTestApprox_contDiff μ hφ.continuous n).differentiable (by simp) x).hasFDerivAt).fderiv
    have hh := congrArg (fun L => L w) h
    change fderiv ℝ (ψ n) x w = _ at hh
    simpa only [ψ, add_apply, smul_apply, smul_eq_mul, mul_comm] using hh
  have hDηφ (x : X) : fderiv ℝ φ x w = η x * fderiv ℝ φ x w + fderiv ℝ η x w * φ x := by
    have h := ((hη.differentiable (by simp) x).hasFDerivAt.mul
      (hφ.differentiable one_ne_zero x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => η y * φ y) x = _ at h
    rw [hηφ] at h
    have hh := congrArg (fun L => L w) h
    simpa only [add_apply, smul_apply, smul_eq_mul, mul_comm] using hh
  have hDψt (x : X) : Tendsto (fun n => fderiv ℝ (ψ n) x w) atTop (𝓝 (fderiv ℝ φ x w)) := by
    simp_rw [hDψ]
    have h := ((tendsto_const_nhds (x := η x)).mul (smoothTestApprox_derivative_tendsto μ hφ hs x w)).add
      ((tendsto_const_nhds (x := fderiv ℝ η x w)).mul (smoothTestApprox_tendsto μ hφ.continuous x))
    rwa [← hDηφ x] at h
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hφ.continuous
  have hDφ : Continuous (fun x => fderiv ℝ φ x w) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨D, hD⟩ := (hs.fderiv_apply ℝ w).exists_bound_of_continuous hDφ
  have hη2 : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hsη
  have hDη2 : MemLp (fun x => fderiv ℝ η x w) 2 μ :=
    ((hη.of_le (by simp) : ContDiff ℝ 1 η).continuous_fderiv one_ne_zero).clm_apply
      continuous_const |>.memLp_of_hasCompactSupport (hsη.fderiv_apply ℝ w)
  have hL : Tendsto (fun n => ∫ x, g x * ψ n x ∂μ) atTop (𝓝 (∫ x, g x * φ x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖ * (‖η x‖ * (3 * B)))
    · intro n
      exact hg.aestronglyMeasurable.mul (hψ n).continuous.aestronglyMeasurable
    · exact hg.norm.integrable_mul (hη2.norm.mul_const _)
    · intro n
      filter_upwards with x
      simp only [ψ, norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (smoothTestApprox_norm_le μ hφ.continuous hB n x) (norm_nonneg _)) (norm_nonneg _)
    · filter_upwards with x
      exact tendsto_const_nhds.mul (hψt x)
  have hR : Tendsto (fun n => ∫ x, u x * fderiv ℝ (ψ n) x w ∂μ) atTop
      (𝓝 (∫ x, u x * fderiv ℝ φ x w ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖u x‖ * (‖η x‖ * (3 * D) + ‖fderiv ℝ η x w‖ * (3 * B)))
    · intro n
      exact hu.aestronglyMeasurable.mul
        ((((hψ n).of_le (by simp) : ContDiff ℝ 1 (ψ n)).continuous_fderiv
          one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
    · exact hu.norm.integrable_mul ((hη2.norm.mul_const _).add (hDη2.norm.mul_const _))
    · intro n
      filter_upwards with x
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [hDψ]
      apply (norm_add_le _ _).trans
      simp only [norm_mul]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [smoothTestApprox_derivative μ hφ hs]
        exact smoothTestApprox_norm_le μ hDφ hD n x
      · exact mul_le_mul_of_nonneg_left
          (smoothTestApprox_norm_le μ hφ.continuous hB n x) (norm_nonneg _)
    · filter_upwards with x
      exact tendsto_const_nhds.mul (hDψt x)
  exact tendsto_nhds_unique hL (hR.neg.congr (fun n => (hweak (ψ n) (hψ n) (hsψ n) (hψΩ n)).symm))

theorem hasWeakDirectionalDerivativeOn_of_smooth
    {Ω : Set X} (hΩ : IsOpen Ω) (u g : X → ℝ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ) (w : X)
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, g x * φ x ∂μ) = -(∫ x, u x * fderiv ℝ φ x w ∂μ)) :
    HasWeakDirectionalDerivativeOn μ Ω w u g := by
  intro φ hφ hs hsub
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
    smooth_test_identity_extends_c1 μ hΩ u g hu hg w hweak φ hφ hs hsub

end OAI.Analysis.PDE.Weak
