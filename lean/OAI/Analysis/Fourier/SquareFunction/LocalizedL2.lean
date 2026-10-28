import OAI.Analysis.Fourier.SquareFunction.LocalSquare
import OAI.Analysis.Fourier.Radial.Kernel
import OAI.Analysis.Fourier.SquareFunction.CubeGeometry

open OAI.Analysis.Fourier.Wave

/-! The localized high-frequency term in the combining-dilates argument.
Only the individual, global `L²` operator bounds are used; the vector bound
comes from finite summation, Cauchy--Schwarz, and actual ball averages. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem enorm_vectorNorm_sq {I H : Type*} [Fintype I] [NormedAddCommGroup H]
    (v : I → H) :
    ENNReal.ofReal (vectorNorm v) ^ (2 : ℝ) = ∑ i, ‖v i‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (vectorNorm_nonneg v), vectorNorm_sq,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖v i‖)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_two]

theorem measurable_vectorNorm {X I H : Type*} [MeasurableSpace X] [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (v : I → X → H) (hv : ∀ i, Measurable (v i)) :
    Measurable (fun x => vectorNorm (fun i => v i x)) := by
  simp only [vectorNorm_eq_sqrt]
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum Finset.univ (fun i _ => (hv i).norm.pow_const 2))

theorem localized_vector_L2_moment {X I H : Type*} [MeasurableSpace X] [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure X) (u : I → X → H) (f : I → X → ℂ)
    (hu : ∀ i, AEStronglyMeasurable (u i) μ) (hf : ∀ i, Measurable (f i))
    {P : Set X} (hP : MeasurableSet P) {B : ℝ≥0∞}
    (h2 : ∀ i, eLpNorm (u i) 2 μ ≤ B * eLpNorm (P.indicator (f i)) 2 μ) :
    (∫⁻ x, ∑ i, ‖u i x‖ₑ ^ (2 : ℝ) ∂μ) ≤
      B ^ (2 : ℝ) * ∫⁻ x in P, ∑ i, ‖f i x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [lintegral_finsetSum' Finset.univ (fun i _ => (hu i).enorm.pow_const 2),
    lintegral_finsetSum Finset.univ (fun i _ => (hf i).enorm.pow_const 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := moment_le_of_eLpNorm_le μ (hu i) ((hf i).indicator hP).aestronglyMeasurable
    (by norm_num : (0 : ℝ) < 2) (by simpa using h2 i)
  have he : (fun x => ‖P.indicator (f i) x‖ₑ ^ (2 : ℝ)) =
      P.indicator (fun x => ‖f i x‖ₑ ^ (2 : ℝ)) := by
    ext x
    by_cases hx : x ∈ P <;> simp [hx]
  rw [he, lintegral_indicator hP] at h
  exact h

/-- An actual localized vector estimate for any ball containing the input
support and the comparison point. `D` records only the ball-to-cube volume
ratio, so the bound is independent of the number of vector components. -/
theorem localized_vector_average_le_maximal {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (u : I → Space n → H) (f : I → Space n → ℂ)
    (hu : ∀ i, Measurable (u i)) (hf : ∀ i, Measurable (f i))
    {Q P : Set (Space n)} (hQ0 : volume Q ≠ 0) (hQtop : volume Q ≠ ∞)
    (hP : MeasurableSet P) {c z : Space n} {R : ℝ}
    (hPball : P ⊆ ball c R) (hz : z ∈ ball c R) {B D : ℝ≥0∞}
    (hvol : volume (ball c R) ≤ D * volume Q)
    (h2 : ∀ i, eLpNorm (u i) 2 volume ≤ B * eLpNorm (P.indicator (f i)) 2 volume) :
    (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x))) / volume Q ≤
      B * (D * ballMaximal volume (fun x => ∑ i, ‖f i x‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) := by
  let F : Space n → ℝ≥0∞ := fun x => ∑ i, ‖f i x‖ₑ ^ (2 : ℝ)
  let M := ballMaximal volume F z
  have hball := euclidean_ball_finite_pos c (nonempty_ball.mp ⟨z, hz⟩)
  have havg : (∫⁻ x in ball c R, F x) ≤ M * volume (ball c R) := by
    apply (ENNReal.div_le_iff_le_mul (.inl hball.1) (.inl hball.2)).mp
    exact le_iSup_of_le (c, R) (le_iSup_of_le hz le_rfl)
  have hmoment : (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x)) ^ (2 : ℝ)) ≤
      B ^ (2 : ℝ) * (M * (D * volume Q)) := by
    simp_rw [enorm_vectorNorm_sq]
    calc
      _ ≤ ∫⁻ x, ∑ i, ‖u i x‖ₑ ^ (2 : ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ B ^ (2 : ℝ) * ∫⁻ x in P, F x :=
        localized_vector_L2_moment volume u f (fun i => (hu i).aestronglyMeasurable) hf hP h2
      _ ≤ B ^ (2 : ℝ) * ∫⁻ x in ball c R, F x :=
        mul_le_mul_right (lintegral_mono' (Measure.restrict_mono_set _ hPball) le_rfl) _
      _ ≤ B ^ (2 : ℝ) * (M * volume (ball c R)) := mul_le_mul_right havg _
      _ ≤ _ := mul_le_mul_right (mul_le_mul_right hvol _) _
  calc
    _ ≤ ((∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x)) ^ (2 : ℝ)) /
        volume Q) ^ (1 / 2 : ℝ) :=
      set_average_le_square_root volume _ (measurable_vectorNorm u hu).ennreal_ofReal Q hQ0 hQtop
    _ ≤ ((B ^ (2 : ℝ) * (M * (D * volume Q))) / volume Q) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.div_le_div_right hmoment _) (by positivity)
    _ = _ := by
      have he : B ^ (2 : ℝ) * (M * (D * volume Q)) =
          (B ^ (2 : ℝ) * (D * M)) * volume Q := by ac_rfl
      rw [he, ENNReal.mul_div_cancel_right hQ0 hQtop,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.rpow_mul]
      norm_num [M, F]

noncomputable def cubeBallRatio (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((8 * ((n : ℝ) + 1)) ^ n) * volume (ball (0 : Space n) 1)

theorem cubeBallRatio_lt_top (n : ℕ) : cubeBallRatio n < ∞ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- The localized high-frequency estimate on a genuine Euclidean cube, with
the dimensional volume constant fully supplied. -/
theorem localized_cube_vector_average {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (Q : BoxIntegral.Box (Fin n)) {s : ℝ} (hs : 0 < s)
    (hside : ∀ i, Q.upper i - Q.lower i = s)
    (u : I → Space n → H) (f : I → Space n → ℂ)
    (hu : ∀ i, Measurable (u i)) (hf : ∀ i, Measurable (f i)) {B : ℝ≥0∞}
    (h2 : ∀ i, eLpNorm (u i) 2 volume ≤ B * eLpNorm
      ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s))).indicator (f i)) 2 volume)
    {z : Space n} (hz : z ∈ euclideanBox Q) :
    (∫⁻ x in euclideanBox Q, ENNReal.ofReal (vectorNorm (fun i => u i x))) /
      volume (euclideanBox Q) ≤
      B * (cubeBallRatio n * ballMaximal volume
        (fun x => ∑ i, ‖f i x‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) := by
  have hzball : z ∈ ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s)) := by
    have hz0 := euclideanBox_subset_ball Q hs hside hz
    have hr : 0 < ((n : ℝ) + 1) * s := by positivity
    exact mem_ball.mpr ((mem_ball.mp hz0).trans_le (by linarith))
  apply localized_vector_average_le_maximal u f hu hf
    (P := ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s)))
    (c := cubeCorner Q) (R := 8 * (((n : ℝ) + 1) * s))
    (by rw [volume_euclideanBox]; exact volume_box_ne_zero Q)
    (by rw [volume_euclideanBox]; exact (Q.measure_coe_lt_top volume).ne)
    isOpen_ball.measurableSet (Subset.refl _) hzball
  · exact (by simpa only [cubeBallRatio, mul_assoc] using
      (volume_enlarged_cube_ball Q hs (show 0 < 8 * ((n : ℝ) + 1) by positivity) hside).le)
  · exact h2

end OAI.Analysis.Fourier.SquareFunction
