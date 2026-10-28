import OAI.Analysis.PDE.Concentration.ForwardSymbol
import Mathlib.Analysis.Fourier.AddCircleMulti

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory
open scoped ComplexConjugate ContDiff

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusFiniteWave {D : Type*} [Fintype D] (s : Finset (D → ℤ)) (a : (D → ℤ) → ℂ) :
    C(UnitAddTorus D, ℂ) := ∑ k ∈ s, a k • UnitAddTorus.mFourier k

theorem integral_sq_torusFiniteWave {D : Type*} [Fintype D]
    (s : Finset (D → ℤ)) (a : (D → ℤ) → ℂ) :
    (∫ x, ‖torusFiniteWave s a x‖ ^ 2) = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  let f := torusFiniteWave s a
  have hf : Integrable (fun x => f x * conj (f x)) := by
    exact (f.continuous.mul f.continuous.star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : inner ℂ (ContinuousMap.toLp 2 volume ℂ f) (ContinuousMap.toLp 2 volume ℂ f) =
      ∑ k ∈ s, conj (a k) * a k := by
    simpa only [f, torusFiniteWave, map_sum, map_smul] using
      UnitAddTorus.orthonormal_mFourier.inner_sum a a s
  rw [ContinuousMap.inner_toLp] at he
  have hr := congrArg (RCLike.re : ℂ → ℝ) he
  rw [← integral_re hf] at hr
  have hre (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simpa only [Complex.mul_conj, Complex.ofReal_re, RCLike.re_to_complex, map_sum,
    Complex.normSq_eq_norm_sq, hre] using hr

/-- Parseval gives an L² multiplier estimate using only the symbol values;
there is no derivative loss in the input-energy bound. -/
theorem torusFiniteMultiplier_L2 {D : Type*} [Fintype D]
    (s : Finset (D → ℤ)) (a b : (D → ℤ) → ℂ) {B : ℝ} (_ : 0 ≤ B)
    (hb : ∀ k ∈ s, ‖b k‖ ≤ B) :
    (∫ x, ‖torusFiniteWave s (fun k => b k * a k) x‖ ^ 2) ≤
      B ^ 2 * ∫ x, ‖torusFiniteWave s a x‖ ^ 2 := by
  rw [integral_sq_torusFiniteWave, integral_sq_torusFiniteWave, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb k hk) 2) (sq_nonneg _)

theorem gaussianForwardSymbol_sup {d : ℕ} (j : Fin 2)
    {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {χ : TransverseSpace d → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L → ∀ η,
        ‖gaussianForwardSymbol j ρ χ h L W η‖ ≤
          C * (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hc⟩ := gaussianForwardSymbol_jets j hρ hcρ hχ hcχ hpos w₀ 0
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL η
  simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, zero_sub] using
    hc W hW h hh L hL 0 (le_refl 0) η

theorem gaussianTorus_L2 {d : ℕ} (j : Fin 2)
    {ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ} {χ : TransverseSpace d → ℂ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hpos : ∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) (w₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : TransverseSpace d, ‖W‖ ≤ w₀ →
      ∀ h : ℝ, 0 < h → ∀ L : ℝ, 1 ≤ L →
      ∀ (s : Finset (Option (Fin d) → ℤ)) (a : (Option (Fin d) → ℤ) → ℂ)
        (η : (Option (Fin d) → ℤ) → OAI.Analysis.Calculus.Current.SpatialSpace d),
      (∫ x, ‖torusFiniteWave s (fun k => gaussianForwardSymbol j ρ χ h L W (η k) * a k) x‖ ^ 2) ≤
        (C * (h ^ d)⁻¹ * L ^ (-(d : ℝ) / 2)) ^ 2 *
          ∫ x, ‖torusFiniteWave s a x‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := gaussianForwardSymbol_sup j hρ hcρ hχ hcχ hpos w₀
  refine ⟨C, hC, ?_⟩
  intro W hW h hh L hL s a η
  exact torusFiniteMultiplier_L2 s a _ (by positivity) (fun k _ => hc W hW h hh L hL (η k))

end OAI.Analysis.PDE.Concentration
