import OAI.Analysis.Fourier.WavePackets.SectorScale
import OAI.Analysis.PDE.Concentration.SectorNormBound

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped ENNReal

local instance sectorFromPDECircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sectorFromPDECircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sectorFromPDECircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Existence of the actual smooth periodic Dirichlet solutions used in
the proof. This is a PDE assertion, not a local-smoothing estimate. -/
def PositivePacketSolvability (n : ℕ) : Prop :=
  ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) (h L : ℝ),
    0 < h → 1 ≤ L → h * L ≤ 1 / 4 →
    ∀ (s : Finset (Fin (n + 2) → ℤ)) (φ : Space (n + 2) → ℂ),
      (∀ k ∈ s, 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k)) →
      ∀ f : UnitAddTorus (Fin (n + 2)) → ℂ,
        Nonempty (OAI.Analysis.PDE.Concentration.SectorPolynomialSolution R h L s φ f)

theorem periodic_sector_bound_of_packet_solvability {n : ℕ}
    (hsolve : PositivePacketSolvability n) {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hKpos : ∀ η ∈ K, 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK η)
    (hKvel : ∀ η ∈ K, ‖OAI.Analysis.PDE.Concentration.gaussianVelocity η‖ ≤ 1 / 40) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C D h₀ : ℝ, 0 < C ∧ 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∀ (R : Space (n + 2) ≃ₗᵢ[ℝ] Space (n + 2)) (φ : Space (n + 2) → ℂ),
          HasCompactSupport φ →
          (∀ ξ ∈ tsupport φ, (OAI.Analysis.PDE.Concentration.spatialFinIsometry (n + 1)).symm (R ξ) ∈ K) →
          (∀ ξ ∈ tsupport φ, Real.sqrt (OAI.Analysis.PDE.Concentration.packetLogScale D h) *
            ‖OAI.Analysis.PDE.Concentration.gaussianVelocity ((OAI.Analysis.PDE.Concentration.spatialFinIsometry (n + 1)).symm (R ξ))‖ ≤ A) →
          ∀ g : UnitAddTorus (Fin (n + 2)) → ℂ,
            let p : ℝ := 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))
            eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 g q.2)
              (.ofReal p) (periodicSpacetimeMeasure (n + 2)) ^ p ≤
            ENNReal.ofReal (C * (1 + Real.log h⁻¹) ^ (p * (3 * ((n : ℝ) + 5) / 2))) *
              (eLpNorm (periodicHalfWave φ h 0 g) ⊤ volume ^ (p - 2) *
                eLpNorm (periodicHalfWave φ h 0 g) 2 volume ^ (2 : ℝ)) := by
  obtain ⟨C, D, hs, hC, hD, hhs, hhs1, hsector⟩ :=
    OAI.Analysis.PDE.Concentration.periodic_sector_norm_bound hK hKpos hKvel A hA
  obtain ⟨hg, hhg, hhg1, hgeom⟩ := exists_small_packetLogScale D
  refine ⟨C, D, min hs hg, hC, hD, lt_min hhs hhg,
    (min_le_left _ _).trans hhs1, ?_⟩
  intro h hh hsmall R φ hc hin hvel g
  dsimp only
  obtain ⟨s, hsamp, hoff⟩ := exists_spectral_index_set hc hh
  have hf (k : Fin (n + 2) → ℤ) (hk : k ∈ s) :
      h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency (packetFrame R) k ∈ K := by
    rw [scaled_orientedPeriodicFrequency_packetFrame]
    exact hin _ (subset_tsupport φ (hsamp k hk))
  have hv (k : Fin (n + 2) → ℤ) (hk : k ∈ s) :
      Real.sqrt (OAI.Analysis.PDE.Concentration.packetLogScale D h) *
        ‖OAI.Analysis.PDE.Concentration.gaussianVelocity (h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency (packetFrame R) k)‖ ≤ A := by
    rw [scaled_orientedPeriodicFrequency_packetFrame]
    exact hvel _ (subset_tsupport φ (hsamp k hk))
  have hh1 : h ≤ 1 := (hsmall.trans (min_le_left _ _)).trans hhs1
  obtain ⟨S⟩ := hsolve (packetFrame R) h (OAI.Analysis.PDE.Concentration.packetLogScale D h) hh
    (one_le_packetLogScale hD hh hh1) (hgeom h hh (hsmall.trans (min_le_right _ _)))
    s φ (fun k hk => hKpos _ (hf k hk)) g
  exact hsector (packetFrame R) h hh (hsmall.trans (min_le_left _ _)) s φ hoff hf hv g S

end OAI.Analysis.Fourier.WavePackets
