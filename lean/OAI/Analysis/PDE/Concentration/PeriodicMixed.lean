import OAI.Analysis.PDE.Concentration.Packet.MixedBound
import OAI.Analysis.PDE.Concentration.TorusCoordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Fourier.WavePackets

local instance periodicMixedCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicMixedCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicMixedCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Restricted-type local smoothing for the actual periodic operator on a
finite narrow-sector Fourier sum. All packet/current/energy estimates and
rotated-cell changes of variables are proved; the remaining PDE premise is
precisely a smooth normalized packet Dirichlet solution. -/
theorem periodic_finite_packet_mixed_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C D h₀ : ℝ, 0 < C ∧ 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt (packetLogScale D h) *
        ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ _ : PhysicalPacketSolution R.toContinuousLinearEquiv h (h * packetLogScale D h) κ
        (fun i => (packetSupNorm κ cR cI v)⁻¹ * cR i)
        (fun i => (packetSupNorm κ cR cI v)⁻¹ * cI i) v (largeBackground (n + 1) h),
      ∀ φ : EuclideanSpace ℝ (Fin (n + 2)) → ℂ,
      (∀ j, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency (fun i => m j (finSuccEquiv (n + 1) i))) = 1) →
      let f := torusIndexedWave (fun j i => m j (finSuccEquiv (n + 1) i))
        (fun j => cR j + cI j * Complex.I)
      (∫ t in (1 : ℝ)..2, ∫ x, ‖OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t f x‖ ^
          (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
        C * (1 + Real.log h⁻¹) ^
          ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) *
          ‖f‖ ^ ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) - 2) *
          (∫ x, ‖f x‖ ^ 2) := by
  obtain ⟨C, D, h₀, hC, hD, hh₀, hh₀1, hmain⟩ :=
    packet_mixed_logarithmic_bound hK hpos hcap A hA
  refine ⟨C, D, h₀, hC, hD, hh₀, hh₀1, ?_⟩
  intro R h hh hsmall ι inst κ cR cI v m hinj hκ hm hf hs S φ hφ
  dsimp only
  have hR (i : Option (Fin (n + 1))) : ‖R.toContinuousLinearEquiv (EuclideanSpace.single i 1)‖ ≤ 1 := by
    change ‖R (EuclideanSpace.single i 1)‖ ≤ 1
    rw [R.norm_map]
    simp
  have hb := hmain R.toContinuousLinearEquiv hR h hh hsmall κ cR cI v m hinj hκ hm hf hs S
  simp_rw [integral_packetBaseWave_eq_periodicHalfWave R κ cR cI v m hinj
    (fun i => (hκ i).le) hm φ h _ hφ
      (fun z : ℂ => ‖z‖ ^ (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))))] at hb
  rw [intervalIntegral.integral_const_mul,
    integral_packetBaseWave_zero_eq_fin_torus R.toContinuousLinearEquiv κ cR cI v m hm
      (fun z : ℂ => ‖z‖ ^ 2),
    packetSupNorm_eq_fin_torus_norm R.toContinuousLinearEquiv κ cR cI v m hm] at hb
  have hJ : 0 < |LinearMap.det (spatialCellMap R.toContinuousLinearEquiv).toLinearMap| := by
    rw [← physicalSpatialCell_volume]
    exact physicalSpatialCell_volume_pos R.toContinuousLinearEquiv
  nlinarith [hb]

end OAI.Analysis.PDE.Concentration
