import OAI.Analysis.PDE.Concentration.Output.X0
import OAI.Analysis.PDE.Concentration.Packet.Normalization

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

/-- The normalized source output estimate. Frequency count, coefficient
bounds, and the large-background size condition are all consequences of
the compact small cap, lattice quantization, and input supremum bound. -/
theorem packet_output_X0_normalized {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ c h₀ L₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ (h L : ℝ), 0 < h → h ≤ h₀ → L₀ ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3 → ℝ,
      ContDiffOn ℝ 2 u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0} →
      ContinuousOn u {x | spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0} →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 → u x ≤ 0) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x)).PosSemidef) →
      (∀ x, spatialDefiningFunction (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (fun w =>
          largeBackground (n + 1) h * spatialBackgroundFunction (n + 1) (OAI.Analysis.PDE.Green.energyComplexTime z) w + u w) x) =
        largeBackground (n + 1) h *
          (physicalLatticeCurrent R h (h * L) κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re) →
      c * h ^ 2 * L ^ (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) *
        (gaussianDerivativeOrder (n + 1) : ℝ)) *
        (∫ y in physicalSpatialCell R,
          ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) (z (0, 0))) y‖ ^
            (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      ∫ x in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
        OAI.Analysis.PDE.Green.physicalSpatialFiber (n + 1) (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z),
        (-u x) * (physicalLatticeCurrent R h (h * L) κ cR cI v
          (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re := by
  obtain ⟨N, hN, hcount⟩ := compact_angular_frequency_count hK
  obtain ⟨F, hF, hfreq⟩ := compact_packet_frequency_bound hK
  have hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1 := by
    intro η hη
    linarith [hcap η hη]
  obtain ⟨c, h₀, L₀, hc, hh₀, hh₀1, hL₀, hbound⟩ :=
    packet_output_X0_lower hK hpos hv A N F 1 hA hN.le hF.le (by norm_num)
  refine ⟨c, h₀, L₀, hc, hh₀, hh₀1, hL₀, ?_⟩
  intro R hR h L hh hsmall hL ι _ κ cR cI v m hinj hκ hm hf hs hnorm
  apply hbound R h L hh hsmall hL κ cR cI v hκ (fun k i => ⟨m k i, hm k i⟩) hf hs
  · apply (le_div_iff₀ (pow_pos hh (n + 2))).mpr
    exact hcount R hR h hh (hsmall.trans hh₀1) _ m hinj hf hm
  · intro k
    exact hfreq (v k) hh (hκ k) (hf k)
  · exact packet_coefficient_le_one R κ cR cI v m hinj hm hnorm
  · intro k
    exact packet_velocity_bound (v k) hh (hκ k) (hcap _ (hf k))

end OAI.Analysis.PDE.Concentration
