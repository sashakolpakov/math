import OAI.Analysis.Fourier.SquareFunction.SharpEnvelope
import OAI.Analysis.Fourier.SquareFunction.VectorMaximal
import OAI.Analysis.Fourier.SquareFunction.LocalizedL2

open OAI.Analysis.Fourier.Wave

/-! The global norms of the maximal envelopes in the combining-dilates
argument, including the square maximal function of the input. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory
open scoped ENNReal

theorem eLpNorm_ofReal_eq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) (p : ℝ≥0∞) :
    eLpNorm (fun x => ENNReal.ofReal (f x)) p μ = eLpNorm f p μ := by
  apply eLpNorm_congr_enorm_ae hf.ennreal_ofReal.aestronglyMeasurable hf.aestronglyMeasurable
  filter_upwards [] with x
  rw [enorm_eq_self, Real.enorm_eq_ofReal (hfn x)]

theorem eLpNorm_square_maximal_le {n : ℕ} {W : Space n → ℝ}
    (hW : Measurable W) (hWn : ∀ x, 0 ≤ W x) {p : ℝ} (hp : 2 < p) :
    eLpNorm (fun x => ballMaximal volume (fun y => ENNReal.ofReal ((W y) ^ 2)) x ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) volume ≤
      (((2 : ℝ≥0∞) ^ (p / 2) * ENNReal.ofReal ((5 : ℝ) ^ n * (p / 2) / (p / 2 - 1))) ^ (1 / p)) *
        eLpNorm W (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have h := eLpNorm_maximal_squares_envelope_le ({()} : Finset Unit) (fun _ => W)
    (fun _ _ => hW) (fun _ _ => hWn) hp
  have he1 : p / 2 * (1 / p) = (1 / 2 : ℝ) := by field_simp
  have he2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [Finset.sum_singleton, ← ENNReal.rpow_mul, he1, he2, ENNReal.rpow_one] at h
  rwa [eLpNorm_ofReal_eq volume hW hWn] at h

theorem ofReal_vectorNorm {I H : Type*} [Fintype I] [NormedAddCommGroup H]
    (v : I → H) : ENNReal.ofReal (vectorNorm v) =
      (∑ i, ‖v i‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [← enorm_vectorNorm_sq, ← ENNReal.rpow_mul]
  norm_num

theorem bounded_vectorNorm {X I H : Type*} [Fintype I] [NormedAddCommGroup H]
    (f : I → X → H) (hf : ∀ i, BddAbove (Set.range fun x => ‖f i x‖)) :
    BddAbove (Set.range fun x => vectorNorm (fun i => f i x)) := by
  choose b hb using hf
  refine ⟨∑ i, b i, ?_⟩
  rintro _ ⟨x, rfl⟩
  apply (vectorNorm_le_sum_norm (fun i => f i x)).trans
  exact Finset.sum_le_sum (fun i _ => hb i ⟨x, rfl⟩)

theorem ballMaximal_ofReal_ne_top_of_bounded {n : ℕ} {f : Space n → ℝ}
    (hf : BddAbove (Set.range f)) (z : Space n) :
    ballMaximal volume (fun x => ENNReal.ofReal (f x)) z ≠ ∞ := by
  obtain ⟨b, hb⟩ := hf
  exact ballMaximal_ne_top_of_bounded ENNReal.ofReal_ne_top
    (fun x => ENNReal.ofReal_le_ofReal (hb ⟨x, rfl⟩)) z

theorem ballMaximal_enorm_sq_ne_top {n : ℕ} {H : Type*} [NormedAddCommGroup H]
    {f : Space n → H} (hf : BddAbove (Set.range fun x => ‖f x‖)) (z : Space n) :
    ballMaximal volume (fun x => ‖f x‖ₑ ^ (2 : ℝ)) z ≠ ∞ := by
  obtain ⟨b, hb⟩ := hf
  apply ballMaximal_ne_top_of_bounded (C := ENNReal.ofReal (max b 0) ^ (2 : ℝ))
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) _ z
  intro x
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((hb ⟨x, rfl⟩).trans (le_max_left _ _))

theorem eLpNorm_ennreal_const_mul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ≥0∞} (hf : Measurable f) (C : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => C * f x) (ENNReal.ofReal p) μ = C * eLpNorm f (ENNReal.ofReal p) μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      (hf.const_mul C).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp.le, enorm_eq_self, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  rw [lintegral_const_mul _ (hf.pow_const p), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem eLpNorm_ennreal_four_add_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b c d : X → ℝ≥0∞) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => a x + b x + c x + d x) p μ ≤
      eLpNorm a p μ + eLpNorm b p μ + eLpNorm c p μ + eLpNorm d p μ := by
  have h₁ := eLpNorm_add_le (f := a) (g := b) (μ := μ) hp
  have h₂ := eLpNorm_add_le (f := fun x => a x + b x) (g := c) (μ := μ) hp
  have h₃ := eLpNorm_add_le (f := fun x => a x + b x + c x) (g := d) (μ := μ) hp
  exact h₃.trans (add_le_add (h₂.trans (add_le_add h₁ le_rfl)) le_rfl)

end OAI.Analysis.Fourier.SquareFunction
