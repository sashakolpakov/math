import OAI.Analysis.Fourier.WavePackets.Periodic
import OAI.Analysis.PDE.Concentration.SpatialL2

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.PDE.Concentration
open scoped ComplexConjugate

local instance finiteFourierCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance finiteFourierCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteFourierCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourierCoeff_torusIndexedWave {D ι : Type*} [Fintype D] [Fintype ι]
    (m : ι → D → ℤ) (a : ι → ℂ) (k : D → ℤ) :
    UnitAddTorus.mFourierCoeff (OAI.Analysis.PDE.Concentration.torusIndexedWave m a) k =
      ∑ i, if m i = k then a i else 0 := by
  classical
  have hi : UnitAddTorus.mFourierCoeff (OAI.Analysis.PDE.Concentration.torusIndexedWave m a) k =
      inner ℂ (UnitAddTorus.mFourierLp 2 k)
        (ContinuousMap.toLp 2 volume ℂ (OAI.Analysis.PDE.Concentration.torusIndexedWave m a)) := by
    rw [ContinuousMap.inner_toLp]
    simp only [UnitAddTorus.mFourierCoeff, ← UnitAddTorus.mFourier_neg, smul_eq_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hi]
  simp only [OAI.Analysis.PDE.Concentration.torusIndexedWave, map_sum, map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier]
  by_cases he : m i = k
  · simp [he]
  · simp [he, Ne.symm he]

theorem mFourierCoeff_torusIndexedWave_at {D ι : Type*} [Fintype D] [Fintype ι]
    (m : ι → D → ℤ) (hm : Function.Injective m) (a : ι → ℂ) (i : ι) :
    UnitAddTorus.mFourierCoeff (OAI.Analysis.PDE.Concentration.torusIndexedWave m a) (m i) = a i := by
  classical
  rw [mFourierCoeff_torusIndexedWave]
  simp [hm.eq_iff]

theorem mFourierCoeff_torusIndexedWave_off {D ι : Type*} [Fintype D] [Fintype ι]
    (m : ι → D → ℤ) (a : ι → ℂ) (k : D → ℤ) (hk : k ∉ Set.range m) :
    UnitAddTorus.mFourierCoeff (OAI.Analysis.PDE.Concentration.torusIndexedWave m a) k = 0 := by
  rw [mFourierCoeff_torusIndexedWave]
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hk ⟨i, h⟩)

/-- On a finite Fourier sum the periodic operator has exactly its expected
finite multiplier formula, including its side-100 frequency normalization. -/
theorem periodicHalfWave_torusIndexedWave {n : ℕ} {ι : Type*} [Fintype ι]
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (h t : ℝ)
    (m : ι → Fin n → ℤ) (hm : Function.Injective m) (a : ι → ℂ)
    (x : UnitAddTorus (Fin n)) :
    periodicHalfWave φ h t (OAI.Analysis.PDE.Concentration.torusIndexedWave m a) x =
      ∑ i, periodicSymbol φ h t (m i) * a i * UnitAddTorus.mFourier (m i) x := by
  classical
  unfold periodicHalfWave
  rw [tsum_eq_sum (s := Finset.univ.image m)]
  · rw [Finset.sum_image (fun i _ j _ hij => hm hij)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mFourierCoeff_torusIndexedWave_at m hm]
  · intro k hk
    have hoff : k ∉ Set.range m := by simpa using hk
    rw [mFourierCoeff_torusIndexedWave_off m a k hoff]
    simp

end OAI.Analysis.Fourier.WavePackets
