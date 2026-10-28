import OAI.Analysis.PDE.Concentration.FiniteSector
import OAI.Analysis.Fourier.WavePackets.SpectralPolynomial

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Fourier.WavePackets

local instance projectedSectorCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance projectedSectorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance projectedSectorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The concrete packet Dirichlet problem attached to the Fourier
coefficients of a finite sector projection. -/
abbrev SectorPolynomialSolution {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h L : ℝ) (s : Finset (Fin (n + 2) → ℤ))
    (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℂ) (f : UnitAddTorus (Fin (n + 2)) → ℂ) :=
  let κ := fun j : s => gaussianFrequencyK (orientedPeriodicFrequency R j.val)
  let v := fun j : s => realGaussianVelocity (orientedPeriodicFrequency R j.val)
  let a := fun j : s => φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency j.val) * UnitAddTorus.mFourierCoeff f j.val
  let P := packetSupNorm κ (fun j => (a j).re) (fun j => (a j).im) v
  PhysicalPacketSolution R.toContinuousLinearEquiv h (h * L) κ
    (fun j => P⁻¹ * (a j).re) (fun j => P⁻¹ * (a j).im) v (largeBackground (n + 1) h)

/-- The restricted mixed estimate for an arbitrary input after actual
compact spectral projection. No finite-polynomial or packet representation
of the input is assumed. -/
theorem periodic_projected_sector_mixed_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C D h₀ : ℝ, 0 < C ∧ 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ (s : Finset (Fin (n + 2) → ℤ)) (φ : EuclideanSpace ℝ (Fin (n + 2)) → ℂ),
      (∀ k ∉ s, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k) = 0) →
      (∀ k ∈ s, h • orientedPeriodicFrequency R k ∈ K) →
      (∀ k ∈ s, Real.sqrt (packetLogScale D h) *
        ‖gaussianVelocity (h • orientedPeriodicFrequency R k)‖ ≤ A) →
      ∀ f : UnitAddTorus (Fin (n + 2)) → ℂ,
      ∀ _ : SectorPolynomialSolution R h (packetLogScale D h) s φ f,
      (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t f x‖ ^
          (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
        C * (1 + Real.log h⁻¹) ^
          ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) *
          ‖OAI.Analysis.Fourier.WavePackets.spectralTorusPolynomial s φ h f‖ ^ ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) - 2) *
          (∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f x‖ ^ 2) := by
  obtain ⟨C, D, h₀, hC, hD, hh₀, hh₀1, hmain⟩ :=
    periodic_finite_sector_mixed_bound hK hpos hcap A hA
  refine ⟨C, D, h₀, hC, hD, hh₀, hh₀1, ?_⟩
  intro R h hh hsmall s φ hoff hf hs f S
  have hb := hmain R h hh hsmall (fun k : s => k.val) Subtype.val_injective
    (fun k => φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency k.val) * UnitAddTorus.mFourierCoeff f k.val)
    (fun k => hf k.val k.property) (fun k => hs k.val k.property) S
  change (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave (fun _ => 1) h t
    (OAI.Analysis.Fourier.WavePackets.spectralTorusPolynomial s φ h f) x‖ ^ _) ≤ _ at hb
  simp_rw [← OAI.Analysis.Fourier.WavePackets.periodicHalfWave_eq_evolve_spectralTorusPolynomial s φ h hoff f] at hb
  rw [OAI.Analysis.Fourier.WavePackets.periodicHalfWave_zero_eq_spectralTorusPolynomial s φ h hoff f]
  exact hb

end OAI.Analysis.PDE.Concentration
