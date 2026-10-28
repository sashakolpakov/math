import OAI.Analysis.Fourier.WavePackets.Amplitude
import OAI.Analysis.Fourier.WavePackets.Lp

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal FourierTransform

noncomputable local instance assemblyCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance assemblyCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance assemblyCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem periodicHalfWave_finset_symbol_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (φ : ι → EuclideanSpace ℝ (Fin n) → ℂ) (hs : ∀ i ∈ s, HasCompactSupport (φ i))
    {h : ℝ} (hh : 0 < h) (T : ℝ) (f : UnitAddTorus (Fin n) → ℂ) :
    periodicHalfWave (∑ i ∈ s, φ i) h T f = ∑ i ∈ s, periodicHalfWave (φ i) h T f := by
  funext x
  have ht := Summable.tsum_finsetSum (fun i hi => summable_periodicHalfWave (hs i hi) hh T f x)
  simpa only [periodicHalfWave, periodicSymbol, Finset.sum_apply, Finset.mul_sum,
    Finset.sum_mul] using ht

theorem mFourierCoeff_finset_input_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → UnitAddTorus (Fin n) → ℂ) (hf : ∀ i ∈ s, Integrable (f i)) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (∑ i ∈ s, f i) k =
      ∑ i ∈ s, UnitAddTorus.mFourierCoeff (f i) k := by
  simp only [UnitAddTorus.mFourierCoeff, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  exact integral_finsetSum s (fun i hi => integrable_mFourier_mul (hf i hi) (-k))

theorem periodicHalfWave_finset_input_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (f : ι → UnitAddTorus (Fin n) → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i)) :
    periodicHalfWave φ h T (∑ i ∈ s, f i) = ∑ i ∈ s, periodicHalfWave φ h T (f i) := by
  funext x
  have ht := Summable.tsum_finsetSum (fun i (_ : i ∈ s) => summable_periodicHalfWave hs hh T (f i) x)
  simpa only [periodicHalfWave, mFourierCoeff_finset_input_sum s f hf,
    Finset.sum_apply, Finset.mul_sum, Finset.sum_mul] using ht

theorem periodicHalfWave_add_input {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f g : UnitAddTorus (Fin n) → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    periodicHalfWave φ h T (f + g) = periodicHalfWave φ h T f + periodicHalfWave φ h T g := by
  have hc (k : Fin n → ℤ) : UnitAddTorus.mFourierCoeff (f + g) k =
      UnitAddTorus.mFourierCoeff f k + UnitAddTorus.mFourierCoeff g k := by
    simp only [UnitAddTorus.mFourierCoeff, Pi.add_apply, smul_eq_mul, mul_add]
    exact integral_add (integrable_mFourier_mul hf (-k)) (integrable_mFourier_mul hg (-k))
  funext x
  simp only [periodicHalfWave, hc, mul_add, add_mul, Pi.add_apply]
  exact (summable_periodicHalfWave hs hh T f x).tsum_add (summable_periodicHalfWave hs hh T g x)

/-- The order of operations in the manuscript: amplitude decomposition
first, and only then frequency projection and half-wave propagation. -/
theorem periodicHalfWave_amplitude_decomposition {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Measurable f) (N : ℕ) (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N) :
    periodicHalfWave φ h T f = periodicHalfWave φ h T (amplitudeTruncation 1 f) +
      ∑ j ∈ Finset.range N, periodicHalfWave φ h T (amplitudePiece j f) := by
  have hsum : Integrable (∑ j ∈ Finset.range N, amplitudePiece j f) := by
    convert integrable_finsetSum (Finset.range N)
      (fun j _ => integrable_amplitudePiece (μ := volume) hf j) using 1
    ext x
    simp only [Finset.sum_apply]
  calc
    _ = periodicHalfWave φ h T (amplitudeTruncation 1 f +
        ∑ j ∈ Finset.range N, amplitudePiece j f) :=
      congrArg (periodicHalfWave φ h T) (amplitude_decomposition f N hN)
    _ = _ := by
      rw [periodicHalfWave_add_input hs hh T (integrable_amplitudeTruncation_one hf) hsum,
        periodicHalfWave_finset_input_sum _ hs hh T _ (fun j _ => integrable_amplitudePiece hf j)]

/-- Summing the actual propagated amplitude pieces costs at most their
number. This is valid for any spacetime observation measure. -/
theorem periodic_amplitude_norm_bound {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    (N : ℕ) (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N)
    {μ : Measure (ℝ × UnitAddTorus (Fin n))} {p D : ℝ≥0∞} (hp : 1 ≤ p)
    (hlo : eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave φ h q.1 (amplitudeTruncation 1 f) q.2) p μ ≤ D)
    (hhi : ∀ j < N, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave φ h q.1 (amplitudePiece j f) q.2) p μ ≤ D) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 f q.2) p μ ≤
      (N + 1 : ℝ≥0∞) * D := by
  have he : (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 f q.2) =
      (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave φ h q.1 (amplitudeTruncation 1 f) q.2) +
      ∑ j ∈ Finset.range N, (fun q : ℝ × UnitAddTorus (Fin n) =>
        periodicHalfWave φ h q.1 (amplitudePiece j f) q.2) := by
    funext q
    rw [periodicHalfWave_amplitude_decomposition hs hh q.1 hf N hN]
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [he]
  calc
    _ ≤ eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
          periodicHalfWave φ h q.1 (amplitudeTruncation 1 f) q.2) p μ +
        eLpNorm (∑ j ∈ Finset.range N, (fun q : ℝ × UnitAddTorus (Fin n) =>
          periodicHalfWave φ h q.1 (amplitudePiece j f) q.2)) p μ := eLpNorm_add_le hp
    _ ≤ D + ∑ _j ∈ Finset.range N, D := add_le_add hlo
      ((eLpNorm_sum_le hp).trans (Finset.sum_le_sum (fun j hj => hhi j (Finset.mem_range.mp hj))))
    _ = _ := by simp [nsmul_eq_mul, add_mul, add_comm]

/-- Finite angular and amplitude decompositions assemble into the genuine
periodic half-wave estimate with precisely the product of their counts. -/
theorem periodic_sector_amplitude_norm_bound {n : ℕ} {ι : Type*} (s : Finset ι)
    (φ : ι → EuclideanSpace ℝ (Fin n) → ℂ) (hs : ∀ i ∈ s, HasCompactSupport (φ i))
    {h : ℝ} (hh : 0 < h) {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    (N : ℕ) (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N)
    {μ : Measure (ℝ × UnitAddTorus (Fin n))} {p D : ℝ≥0∞} (hp : 1 ≤ p)
    (hlo : ∀ i ∈ s, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (φ i) h q.1 (amplitudeTruncation 1 f) q.2) p μ ≤ D)
    (hhi : ∀ i ∈ s, ∀ j < N, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (φ i) h q.1 (amplitudePiece j f) q.2) p μ ≤ D) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (∑ i ∈ s, φ i) h q.1 f q.2) p μ ≤
      (s.card : ℝ≥0∞) * (N + 1 : ℝ≥0∞) * D := by
  have he : (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (∑ i ∈ s, φ i) h q.1 f q.2) =
      ∑ i ∈ s, (fun q : ℝ × UnitAddTorus (Fin n) => periodicHalfWave (φ i) h q.1 f q.2) := by
    funext q
    rw [periodicHalfWave_finset_symbol_sum s φ hs hh]
    simp only [Finset.sum_apply]
  rw [he]
  calc
    _ ≤ ∑ i ∈ s, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
        periodicHalfWave (φ i) h q.1 f q.2) p μ := eLpNorm_sum_le hp
    _ ≤ ∑ _i ∈ s, (N + 1 : ℝ≥0∞) * D := Finset.sum_le_sum fun i hi =>
      periodic_amplitude_norm_bound (hs i hi) hh hf N hN hp (hlo i hi) (hhi i hi)
    _ = _ := by simp [nsmul_eq_mul, mul_assoc]

theorem combined_logarithmic_loss {n : ℕ} (hn : 1 ≤ n) (L : ℝ≥0∞) :
    L ^ (((n : ℝ) - 1) / 2) * L ^ (1 : ℝ) * L ^ (3 * ((n : ℝ) + 3) / 2) =
      L ^ (2 * (n : ℝ) + 5) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num),
    ← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith)]
  congr 1
  ring

/-- The sector count, amplitude count, and restricted-sector loss yield
exactly the manuscript's exponent `2n + 5`. All norms here belong to the
actual periodic half-wave and all decomposition identities are proved. -/
theorem periodic_logarithmic_bound_of_piece_bounds {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} (s : Finset ι) (φ : ι → EuclideanSpace ℝ (Fin n) → ℂ)
    (hs : ∀ i ∈ s, HasCompactSupport (φ i)) {h : ℝ} (hh : 0 < h)
    {f : UnitAddTorus (Fin n) → ℂ} (hf : Measurable f)
    (N : ℕ) (hN : ∀ x, ‖f x‖ < (2 : ℝ) ^ N)
    {μ : Measure (ℝ × UnitAddTorus (Fin n))} {p L C₀ C₁ C₂ F : ℝ≥0∞} (hp : 1 ≤ p)
    (hsectors : (s.card : ℝ≥0∞) ≤ C₁ * L ^ (((n : ℝ) - 1) / 2))
    (hlevels : (N + 1 : ℝ≥0∞) ≤ C₂ * L)
    (hlo : ∀ i ∈ s, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (φ i) h q.1 (amplitudeTruncation 1 f) q.2) p μ ≤
        C₀ * L ^ (3 * ((n : ℝ) + 3) / 2) * F)
    (hhi : ∀ i ∈ s, ∀ j < N, eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (φ i) h q.1 (amplitudePiece j f) q.2) p μ ≤
        C₀ * L ^ (3 * ((n : ℝ) + 3) / 2) * F) :
    eLpNorm (fun q : ℝ × UnitAddTorus (Fin n) =>
      periodicHalfWave (∑ i ∈ s, φ i) h q.1 f q.2) p μ ≤
      (C₁ * C₂ * C₀) * L ^ (2 * (n : ℝ) + 5) * F := by
  calc
    _ ≤ (s.card : ℝ≥0∞) * (N + 1 : ℝ≥0∞) *
        (C₀ * L ^ (3 * ((n : ℝ) + 3) / 2) * F) :=
      periodic_sector_amplitude_norm_bound s φ hs hh hf N hN hp hlo hhi
    _ ≤ (C₁ * L ^ (((n : ℝ) - 1) / 2)) * (C₂ * L) *
        (C₀ * L ^ (3 * ((n : ℝ) + 3) / 2) * F) :=
      mul_le_mul' (mul_le_mul' hsectors hlevels) le_rfl
    _ = (C₁ * C₂ * C₀) *
        (L ^ (((n : ℝ) - 1) / 2) * L ^ (1 : ℝ) * L ^ (3 * ((n : ℝ) + 3) / 2)) * F := by
      rw [ENNReal.rpow_one]
      ac_rfl
    _ = _ := by rw [combined_logarithmic_loss hn]

end OAI.Analysis.Fourier.WavePackets
