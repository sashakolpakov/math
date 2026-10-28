import OAI.Analysis.PDE.Weak.Boundary.Weak.NormalComponents

/-! Scalar L² distributional algebra used in recovering the normal
second derivative from the divergence-form equation. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsLocallyFiniteMeasure μ]

omit [NormedSpace ℝ X] [SecondCountableTopology X] [IsLocallyFiniteMeasure μ] in
theorem memLp_bounded_scalar_mul {a u : X → ℝ} (ha : Continuous a)
    (hu : MemLp u 2 μ) {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C) :
    MemLp (fun x => a x * u x) 2 μ := by
  apply hu.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards with x
  change ‖a x * u x‖ ≤ C * ‖u x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

omit [BorelSpace X] [SecondCountableTopology X] [IsLocallyFiniteMeasure μ] in
theorem HasWeakDirectionalDerivativeOn.scalar_identity
    {Ω : Set X} {w : X} {u g : X → ℝ}
    (hd : HasWeakDirectionalDerivativeOn μ Ω w u g)
    (φ : X → ℝ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ) (hsub : tsupport φ ⊆ Ω) :
    (∫ x, g x * φ x ∂μ) = -(∫ x, u x * fderiv ℝ φ x w ∂μ) := by
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hd φ hφ hs hsub

omit [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.scalar_sub
    {Ω : Set X} {w : X} {u v g h : X → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hd : HasWeakDirectionalDerivativeOn μ Ω w u g)
    (he : HasWeakDirectionalDerivativeOn μ Ω w v h) :
    HasWeakDirectionalDerivativeOn μ Ω w (fun x => u x - v x) (fun x => g x - h x) := by
  intro φ hφ hs hsub
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hs
  have hDφ2 : MemLp (fun x => fderiv ℝ φ x w) 2 μ :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ w)
  have hd' := hd.scalar_identity μ φ hφ hs hsub
  have he' := he.scalar_identity μ φ hφ hs hsub
  have hl : (∫ x, (g x - h x) * φ x ∂μ) =
      (∫ x, g x * φ x ∂μ) - ∫ x, h x * φ x ∂μ := by
    simp_rw [sub_mul]
    exact integral_sub (hg.integrable_mul hφ2) (hh.integrable_mul hφ2)
  have hr : (∫ x, (u x - v x) * fderiv ℝ φ x w ∂μ) =
      (∫ x, u x * fderiv ℝ φ x w ∂μ) - ∫ x, v x * fderiv ℝ φ x w ∂μ := by
    simp_rw [sub_mul]
    exact integral_sub (hu.integrable_mul hDφ2) (hv.integrable_mul hDφ2)
  have hf : (∫ x, (g x - h x) * φ x ∂μ) = -(∫ x, (u x - v x) * fderiv ℝ φ x w ∂μ) := by
    rw [hl, hr, hd', he']
    ring
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hf

omit [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.scalar_finset_sum
    {ι : Type*} (s : Finset ι) {Ω : Set X} {w : X} (u g : ι → X → ℝ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 μ) (hg : ∀ i ∈ s, MemLp (g i) 2 μ)
    (hd : ∀ i ∈ s, HasWeakDirectionalDerivativeOn μ Ω w (u i) (g i)) :
    HasWeakDirectionalDerivativeOn μ Ω w (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, g i x) := by
  intro φ hφ hs hsub
  have hφ2 : MemLp φ 2 μ := hφ.continuous.memLp_of_hasCompactSupport hs
  have hDφ2 : MemLp (fun x => fderiv ℝ φ x w) 2 μ :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hs.fderiv_apply ℝ w)
  have he : (∫ x, (∑ i ∈ s, g i x) * φ x ∂μ) =
      -(∫ x, (∑ i ∈ s, u i x) * fderiv ℝ φ x w ∂μ) := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum s (f := fun i x => g i x * φ x) (fun i hi => (hg i hi).integrable_mul hφ2),
      integral_finsetSum s (f := fun i x => u i x * fderiv ℝ φ x w)
        (fun i hi => (hu i hi).integrable_mul hDφ2), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i hi => (hd i hi).scalar_identity μ φ hφ hs hsub)
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using he

end OAI.Analysis.PDE.Weak
