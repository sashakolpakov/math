import OAI.Analysis.Fourier.WavePackets.FiniteFourier

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.PDE.Concentration

local instance spectralPolynomialCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance spectralPolynomialCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance spectralPolynomialCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def spectralTorusPolynomial {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ) (f : UnitAddTorus (Fin n) → ℂ) :
    C(UnitAddTorus (Fin n), ℂ) :=
  OAI.Analysis.PDE.Concentration.torusIndexedWave (fun k : s => k.val)
    (fun k => φ (h • periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val)

theorem periodicHalfWave_eq_finite_sum {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) (t : ℝ) (x : UnitAddTorus (Fin n)) :
    periodicHalfWave φ h t f x =
      ∑ k : s, Complex.exp (-Complex.I * ((t * ‖periodicFrequency k.val‖ : ℝ) : ℂ)) *
        (φ (h • periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val) *
          UnitAddTorus.mFourier k.val x := by
  rw [Finset.sum_coe_sort s (fun k : Fin n → ℤ =>
    Complex.exp (-Complex.I * ((t * ‖periodicFrequency k‖ : ℝ) : ℂ)) *
      (φ (h • periodicFrequency k) * UnitAddTorus.mFourierCoeff f k) * UnitAddTorus.mFourier k x)]
  unfold periodicHalfWave
  rw [tsum_eq_sum (s := s)]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [periodicSymbol]
    ring
  · intro k hk
    simp [periodicSymbol, hs k hk]

theorem periodicHalfWave_zero_eq_spectralTorusPolynomial {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • periodicFrequency k) = 0) (f : UnitAddTorus (Fin n) → ℂ) :
    periodicHalfWave φ h 0 f = spectralTorusPolynomial s φ h f := by
  funext x
  rw [periodicHalfWave_eq_finite_sum s φ h hs]
  simp [spectralTorusPolynomial, OAI.Analysis.PDE.Concentration.torusIndexedWave]

/-- A compact spectral projection is an actual finite polynomial. Evolving
it by the uncut half-wave is exactly the original localized operator. -/
theorem periodicHalfWave_eq_evolve_spectralTorusPolynomial {n : ℕ} (s : Finset (Fin n → ℤ))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h : ℝ)
    (hs : ∀ k ∉ s, φ (h • periodicFrequency k) = 0)
    (f : UnitAddTorus (Fin n) → ℂ) (t : ℝ) (x : UnitAddTorus (Fin n)) :
    periodicHalfWave φ h t f x =
      periodicHalfWave (fun _ => 1) h t (spectralTorusPolynomial s φ h f) x := by
  rw [periodicHalfWave_eq_finite_sum s φ h hs]
  unfold spectralTorusPolynomial
  rw [periodicHalfWave_torusIndexedWave _ h t _ Subtype.val_injective]
  simp only [periodicSymbol, mul_one]

theorem exists_spectral_index_set {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) :
    ∃ s : Finset (Fin n → ℤ),
      (∀ k ∈ s, φ (h • periodicFrequency k) ≠ 0) ∧
      (∀ k ∉ s, φ (h • periodicFrequency k) = 0) := by
  classical
  have hf : (Function.support (fun k => φ (h • periodicFrequency k))).Finite := by
    simpa only [periodicFrequency, smul_smul] using
      finite_support_lattice_sample hφ (show 0 < h * (2 * Real.pi / 100) by positivity)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro k hk
    exact hf.mem_toFinset.mp hk
  · intro k hk
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hk

end OAI.Analysis.Fourier.WavePackets
