import OAI.Analysis.PDE.Concentration.PeriodicNorm

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Fourier.WavePackets
open scoped ENNReal

local instance sectorNormCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sectorNormCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sectorNormCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual narrow-sector estimate in the exact extended-norm form
needed by the amplitude and angular-sector assembly. The only PDE input is
the displayed, concretely constructed normalized packet solution. -/
theorem periodic_sector_norm_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
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
      let p : ℝ := 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))
      eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h q.1 f q.2)
        (.ofReal p) (OAI.Analysis.Fourier.WavePackets.periodicSpacetimeMeasure (n + 2)) ^ p ≤
        ENNReal.ofReal (C * (1 + Real.log h⁻¹) ^ (p * (3 * ((n : ℝ) + 5) / 2))) *
          (eLpNorm (OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f) ⊤ volume ^ (p - 2) *
            eLpNorm (OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h 0 f) 2 volume ^ (2 : ℝ)) := by
  obtain ⟨C, D, h₀, hC, hD, hh₀, hh₀1, hmain⟩ :=
    periodic_projected_sector_mixed_bound hK hpos hcap A hA
  refine ⟨C, D, h₀, hC, hD, hh₀, hh₀1, ?_⟩
  intro R h hh hsmall s φ hoff hf hs f S
  dsimp only
  have hp : 2 ≤ 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hq : 1 ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) := (le_div_iff₀ hn).mpr (by linarith)
    linarith
  have hlog : 0 ≤ 1 + Real.log h⁻¹ := by
    have hl := Real.log_nonneg ((one_le_inv₀ hh).mpr (hsmall.trans hh₀1))
    linarith
  exact periodic_mixed_bound_ennreal s φ h hoff f hp
    (mul_nonneg hC.le (Real.rpow_nonneg hlog _))
    (hmain R h hh hsmall s φ hoff hf hs f S)

end OAI.Analysis.PDE.Concentration
