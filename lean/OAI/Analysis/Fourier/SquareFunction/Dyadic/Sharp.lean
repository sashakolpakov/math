import OAI.Analysis.Fourier.SquareFunction.Dyadic.GoodLambda
import OAI.Analysis.Fourier.SquareFunction.Dyadic.Boxes

/-! Finite-level dyadic sharp-function estimates, with the root-average term
kept explicitly for subsequent passage to the whole space. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

private theorem ofReal_lt_finite_iff {r : ℝ} (hr : 0 ≤ r) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.ofReal r < a ↔ r < a.toReal := by
  rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ha, ENNReal.toReal_ofReal hr]

/-- The finite-level sharp estimate. Its constants do not depend on the number
of scales. Only the root average remains in addition to the sharp function. -/
theorem finite_dyadic_sharp_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hfn : ∀ x, 0 ≤ f x)
    (s : Finset (Set X)) (hs : IsLaminar s)
    (hm : ∀ Q ∈ s, MeasurableSet Q) (hQ0 : ∀ Q ∈ s, μ Q ≠ 0)
    (hmean : ∀ Q ∈ s, positiveSetMean μ f Q ≠ ∞)
    (hosc : ∀ Q ∈ s, setOscillation μ f Q ≠ ∞)
    (root : Set X) (hrootfin : positiveSetMean μ f root ≠ ∞)
    {D p γ : ℝ} (hD : 0 ≤ D) (hp : 0 < p) (hγ : 0 < γ)
    (hsmall : γ * (D + 1) ^ p < 1)
    (hparent : ∀ Q ∈ s, Q ≠ root → ∃ P ∈ s, Q ⊂ P ∧ μ P ≤ ENNReal.ofReal D * μ Q) :
    (∫⁻ x, familySup s (positiveSetMean μ f) x ^ p ∂μ) ≤
      ENNReal.ofReal (1 / (1 - γ * (D + 1) ^ p)) *
        ∫⁻ x, ENNReal.ofReal (max
          ((D + 1) * ((familySup s (setOscillation μ f) x).toReal / γ))
          ((D + 1) * (positiveSetMean μ f root).toReal)) ^ p ∂μ := by
  let A := D + 1
  have hA : 0 < A := by dsimp [A]; linarith
  let M := familySup s (positiveSetMean μ f)
  let S := familySup s (setOscillation μ f)
  let u : X → ℝ := fun x => (M x).toReal
  let v : X → ℝ := fun x => max (A * ((S x).toReal / γ))
    (A * (positiveSetMean μ f root).toReal)
  have hMfin : ∀ x, M x ≠ ∞ := familySup_ne_top s _ hmean
  have hSfin : ∀ x, S x ≠ ∞ := familySup_ne_top s _ hosc
  have hu : Measurable u := (measurable_familySup s hm _).ennreal_toReal
  have hv : Measurable v :=
    (measurable_const.mul ((measurable_familySup s hm _).ennreal_toReal.div_const γ)).max
      measurable_const
  have hun : ∀ x, 0 ≤ u x := fun _ => ENNReal.toReal_nonneg
  have hvn : ∀ x, 0 ≤ v x := fun x => (mul_nonneg hA.le
    (div_nonneg ENNReal.toReal_nonneg hγ.le)).trans (le_max_left _ _)
  have hgood (t : ℝ) (ht : 0 < t) : μ {x | t < u x} ≤
      μ {x | t < v x} + ENNReal.ofReal γ * μ {x | t < A * u x} := by
    let r := t / A
    have hr : 0 < r := div_pos ht hA
    have htr : A * r = t := mul_div_cancel₀ t hA.ne'
    by_cases hroot : positiveSetMean μ f root ≤ ENNReal.ofReal r
    · have hd := finite_dyadic_distribution μ f hfn s hs hm hQ0
        (fun Q _ => measure_ne_top μ Q) hmean root
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top hroot hparent
        (γ := ENNReal.ofReal γ)
      have hβ : ENNReal.ofReal D * ENNReal.ofReal r + ENNReal.ofReal r =
          ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_add (mul_nonneg hD hr.le) hr.le]
        congr 1
        dsimp [A] at htr
        nlinarith
      have hhigh : {x | ENNReal.ofReal D * ENNReal.ofReal r + ENNReal.ofReal r < M x} =
          {x | t < u x} := by
        ext x
        rw [hβ]
        exact ofReal_lt_finite_iff ht.le (hMfin x)
      have hlow : {x | ENNReal.ofReal r < M x} = {x | t < A * u x} := by
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ofReal_lt_finite_iff hr.le (hMfin x)]
        change r < u x ↔ t < A * u x
        rw [← htr, mul_lt_mul_iff_right₀ hA]
      have hsharp : {x | ENNReal.ofReal γ * ENNReal.ofReal r < S x} ⊆
          {x | t < v x} := by
        intro x hx
        rw [← ENNReal.ofReal_mul hγ.le] at hx
        have hx' := (ofReal_lt_finite_iff (mul_nonneg hγ.le hr.le) (hSfin x)).mp hx
        have hdiv : r < (S x).toReal / γ := (lt_div_iff₀ hγ).mpr (by simpa [mul_comm] using hx')
        have hh : t < A * ((S x).toReal / γ) := by
          rw [← htr]
          exact mul_lt_mul_of_pos_left hdiv hA
        exact hh.trans_le (le_max_left _ _)
      change μ {x | ENNReal.ofReal D * ENNReal.ofReal r + ENNReal.ofReal r < M x} ≤
        μ {x | ENNReal.ofReal γ * ENNReal.ofReal r < S x} +
          ENNReal.ofReal γ * μ {x | ENNReal.ofReal r < M x} at hd
      rw [hhigh, hlow] at hd
      exact hd.trans (add_le_add (measure_mono hsharp) le_rfl)
    · have hh : r < (positiveSetMean μ f root).toReal :=
        (ofReal_lt_finite_iff hr.le hrootfin).mp (lt_of_not_ge hroot)
      have htroot : t < A * (positiveSetMean μ f root).toReal := by
        rw [← htr]
        exact mul_lt_mul_of_pos_left hh hA
      have hsub : {x | t < u x} ⊆ {x | t < v x} :=
        fun _ _ => htroot.trans_le (le_max_right _ _)
      exact (measure_mono hsub).trans (le_add_of_nonneg_right bot_le)
  have hfin : (∫⁻ x, ENNReal.ofReal (u x) ^ p ∂μ) < ∞ := by
    simp_rw [show ∀ x, ENNReal.ofReal (u x) = M x from fun x => ENNReal.ofReal_toReal (hMfin x)]
    exact familySup_power_integral_lt_top μ s _ hmean hp.le
  have h := power_moment_le_of_good_lambda μ hu hv hun hvn hp hA.le hγ.le hsmall hfin hgood
  simpa only [show ∀ x, ENNReal.ofReal (u x) = M x from fun x => ENNReal.ofReal_toReal (hMfin x)] using h

end OAI.Analysis.Fourier.SquareFunction
