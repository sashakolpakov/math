import OAI.Analysis.Fourier.SquareFunction.EuclideanSharp
import OAI.Analysis.Fourier.SquareFunction.VectorMaximal

/-! Finite-vector inequalities and normalized Cauchy--Schwarz for oscillation. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem laverage_le_square_root {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f)
    (hμ0 : μ Set.univ ≠ 0) (hμtop : μ Set.univ ≠ ∞) :
    (⨍⁻ x, f x ∂μ) ≤ (⨍⁻ x, f x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  let ν : Measure X := (μ Set.univ)⁻¹ • μ
  have hν : ν Set.univ = 1 := by
    simp only [ν, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ0 hμtop]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (f := f) (g := fun _ => 1) hf.aemeasurable measurable_const.aemeasurable
  simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul, hν,
    laverage, ν] using h

theorem set_average_le_square_root {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) (Q : Set X)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞) :
    (∫⁻ x in Q, f x ∂μ) / μ Q ≤
      ((∫⁻ x in Q, f x ^ (2 : ℝ) ∂μ) / μ Q) ^ (1 / 2 : ℝ) := by
  rw [← setLAverage_eq, ← setLAverage_eq]
  exact laverage_le_square_root (μ.restrict Q) f hf (by simpa) (by simpa)

noncomputable def vectorNorm {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) : ℝ := ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : I => H))‖

theorem vectorNorm_eq_sqrt {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) : vectorNorm v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  exact PiLp.norm_eq_of_L2 _

theorem vectorNorm_nonneg {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) : 0 ≤ vectorNorm v := norm_nonneg _

theorem vectorNorm_sq {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) : vectorNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 (fun _ : I => H) _

theorem abs_vectorNorm_sub_le {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v w : I → H) : |vectorNorm v - vectorNorm w| ≤ vectorNorm (fun i => v i - w i) := by
  exact abs_norm_sub_norm_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

theorem vectorNorm_add_le {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v w : I → H) : vectorNorm (fun i => v i + w i) ≤ vectorNorm v + vectorNorm w := by
  exact norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

/-- Componentwise geometric gains combine in their `ℓ²` norm, without a
factor depending on the number of scales. -/
theorem vectorNorm_le_weighted {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) (a : I → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, ‖v i‖ ≤ a i * c) :
    vectorNorm v ≤ Real.sqrt (∑ i, a i ^ 2) * c := by
  rw [vectorNorm_eq_sqrt]
  calc
    _ ≤ Real.sqrt (∑ i, (a i * c) ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (ha i) hc)).mpr (hv i))
    _ = Real.sqrt ((∑ i, a i ^ 2) * c ^ 2) := by
      congr 1
      simp only [mul_pow, Finset.sum_mul]
    _ = _ := by
      rw [Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))), Real.sqrt_sq hc]

theorem vectorNorm_le_sum_norm {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (v : I → H) : vectorNorm v ≤ ∑ i, ‖v i‖ := by
  rw [vectorNorm_eq_sqrt]
  exact (Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => norm_nonneg (v i)))).trans_eq
      (Real.sqrt_sq (Finset.sum_nonneg (fun i _ => norm_nonneg (v i))))

theorem continuous_vectorNorm {X I H : Type*} [TopologicalSpace X] [Fintype I]
    [SeminormedAddCommGroup H] (v : I → X → H) (hv : ∀ i, Continuous (v i)) :
    Continuous (fun x => vectorNorm (fun i => v i x)) := by
  simp only [vectorNorm_eq_sqrt]
  exact Real.continuous_sqrt.comp (continuous_finsetSum Finset.univ (fun i _ => (hv i).norm.pow 2))

theorem integrable_vectorNorm {X I H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [Fintype I] [NormedAddCommGroup H]
    (μ : Measure X) (v : I → X → H) (hvc : ∀ i, Continuous (v i)) (hv : ∀ i, Integrable (v i) μ) :
    Integrable (fun x => vectorNorm (fun i => v i x)) μ := by
  apply (integrable_finsetSum Finset.univ (fun i _ => (hv i).norm)).mono'
    (continuous_vectorNorm v hvc).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (vectorNorm_nonneg _)]
  exact vectorNorm_le_sum_norm _

theorem vectorNorm_mono {I H G : Type*} [Fintype I]
    [SeminormedAddCommGroup H] [SeminormedAddCommGroup G]
    (v : I → H) (w : I → G) (h : ∀ i, ‖v i‖ ≤ ‖w i‖) :
    vectorNorm v ≤ vectorNorm w := by
  rw [vectorNorm_eq_sqrt, vectorNorm_eq_sqrt]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (h i))

theorem component_norm_le_vectorNorm {I H : Type*} [Fintype I]
    [SeminormedAddCommGroup H] (v : I → H) (i : I) : ‖v i‖ ≤ vectorNorm v :=
  PiLp.norm_apply_le (WithLp.toLp 2 v) i

theorem vectorNorm_four_add_le {I H : Type*} [Fintype I] [SeminormedAddCommGroup H]
    (a b c d : I → H) :
    vectorNorm (fun i => a i + b i + c i + d i) ≤
      vectorNorm a + vectorNorm b + vectorNorm c + vectorNorm d := by
  have hab := vectorNorm_add_le a b
  have habc := vectorNorm_add_le (fun i => a i + b i) c
  have habcd := vectorNorm_add_le (fun i => a i + b i + c i) d
  exact habcd.trans (add_le_add (habc.trans (add_le_add hab le_rfl)) le_rfl)

end OAI.Analysis.Fourier.SquareFunction
