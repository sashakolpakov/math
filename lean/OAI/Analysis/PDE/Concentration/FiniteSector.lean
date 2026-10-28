import OAI.Analysis.PDE.Concentration.PeriodicMixed
import OAI.Analysis.PDE.Concentration.FrequencyParameters

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Fourier.WavePackets

local instance finiteSectorCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance finiteSectorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance finiteSectorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual finite-sector theorem, stated directly for integer torus
frequencies and complex Fourier coefficients. The null packet parameters
are constructed from the frequencies rather than separately assumed. -/
theorem periodic_finite_sector_mixed_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C D h₀ : ℝ, 0 < C ∧ 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ {ι : Type} [Fintype ι] (m : ι → Fin (n + 2) → ℤ), Function.Injective m →
      ∀ a : ι → ℂ,
      (∀ j, h • orientedPeriodicFrequency R (m j) ∈ K) →
      (∀ j, Real.sqrt (packetLogScale D h) *
        ‖gaussianVelocity (h • orientedPeriodicFrequency R (m j))‖ ≤ A) →
      let κ := fun j => gaussianFrequencyK (orientedPeriodicFrequency R (m j))
      let v := fun j => realGaussianVelocity (orientedPeriodicFrequency R (m j))
      let P := packetSupNorm κ (fun j => (a j).re) (fun j => (a j).im) v
      ∀ _ : PhysicalPacketSolution R.toContinuousLinearEquiv h (h * packetLogScale D h) κ
        (fun j => P⁻¹ * (a j).re) (fun j => P⁻¹ * (a j).im) v (largeBackground (n + 1) h),
      (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave (fun _ => 1) h t (torusIndexedWave m a) x‖ ^
          (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
        C * (1 + Real.log h⁻¹) ^
          ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) *
          ‖torusIndexedWave m a‖ ^ ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) - 2) *
          (∫ x, ‖torusIndexedWave m a x‖ ^ 2) := by
  obtain ⟨C, D, h₀, hC, hD, hh₀, hh₀1, hmain⟩ :=
    periodic_finite_packet_mixed_bound hK hpos hcap A hA
  refine ⟨C, D, h₀, hC, hD, hh₀, hh₀1, ?_⟩
  intro R h hh hsmall ι inst m hinj a hf hs
  dsimp only
  intro S
  let κ := fun j => gaussianFrequencyK (orientedPeriodicFrequency R (m j))
  let v := fun j => realGaussianVelocity (orientedPeriodicFrequency R (m j))
  let mo := fun j i => m j ((finSuccEquiv (n + 1)).symm i)
  have hκ (j : ι) : 0 < κ j := by
    have hp := hpos _ (hf j)
    rw [gaussianFrequencyK_smul hh.le] at hp
    dsimp [κ]
    nlinarith
  have he (j : ι) : packetSpatialFrequency (κ j) (v j) = orientedPeriodicFrequency R (m j) :=
    packet_frequency_parameters _ (hκ j)
  have hm : Function.Injective mo := by
    intro i j hij
    apply hinj
    funext k
    have hk := congrFun hij (finSuccEquiv (n + 1) k)
    simpa only [mo, Equiv.symm_apply_apply] using hk
  have hq (j : ι) (i : Option (Fin (n + 1))) :
      inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
        (mo j i : ℝ) * (2 * Real.pi) / 100 := by
    rw [he]
    exact orientedPeriodicFrequency_quantized R (m j) i
  have hb := hmain R h hh hsmall κ (fun j => (a j).re) (fun j => (a j).im) v mo hm hκ hq
    (fun j => by rw [he]; exact hf j)
    (fun j => by rw [he]; exact hs j) S (fun _ => 1) (fun _ => rfl)
  simpa only [mo, Equiv.symm_apply_apply, Complex.re_add_im] using hb

end OAI.Analysis.PDE.Concentration
