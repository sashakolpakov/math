import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Family
import OAI.Analysis.Fourier.WavePackets.SectorFromPDE

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology

theorem sector_frequency_positive {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    {h : ℝ} (hh : 0 < h) (k : Fin (n+2) → ℤ)
    (hk : 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k)) :
    0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k) := by
  rw [OAI.Analysis.PDE.Concentration.gaussianFrequencyK_smul hh.le] at hk
  exact (mul_pos_iff_of_pos_left hh).mp hk

/-- The spectral packet parameters inherit the exact side-100 lattice,
including after the sector rotation. -/
theorem sector_frequency_quantized {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (k : Fin (n+2) → ℤ) (hk : 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k))
    (j : Fin (n+2)) :
    inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (OAI.Analysis.PDE.Concentration.gaussianFrequencyK (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k))
      (OAI.Analysis.PDE.Concentration.realGaussianVelocity (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k)))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) =
        (k j : ℝ)*(2*Real.pi)/100 := by
  rw [OAI.Analysis.PDE.Concentration.packet_frequency_parameters _ hk]
  simpa only [Equiv.symm_apply_apply] using
    OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency_quantized R k (finSuccEquiv (n+1) j)

def packetParameterOne : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 := EuclideanSpace.single (0,1) 1

theorem energyComplexTime_packetParameterOne : OAI.Analysis.PDE.Green.energyComplexTime packetParameterOne = 1 := by
  simp [OAI.Analysis.PDE.Green.energyComplexTime,packetParameterOne]

theorem packetParameterOne_mem_annulus {a : ℝ} (ha : a ≤ 1/4) :
    packetParameterOne ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
  change a < ‖OAI.Analysis.PDE.Green.energyComplexTime packetParameterOne‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime packetParameterOne‖ < 4
  rw [energyComplexTime_packetParameterOne,norm_one]
  constructor <;> linarith

/-- The exact normalized finite-sector coefficients determine a genuine
family of spatial Dirichlet solutions and locally uniform barriers.
No size or nonvanishing assumption on the input polynomial is needed. -/
theorem nonempty_sector_packet_family {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1)) (h L : ℝ)
    (hh : 0 < h) (hL : 1 ≤ L) (hsmall : h*L ≤ 1/4)
    (s : Finset (Fin (n+2) → ℤ)) (φ : Space (n+2) → ℂ)
    (hpos : ∀ k ∈ s, 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k))
    (f : UnitAddTorus (Fin (n+2)) → ℂ) :
    let κ := fun j : s => OAI.Analysis.PDE.Concentration.gaussianFrequencyK (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R j.val)
    let v := fun j : s => OAI.Analysis.PDE.Concentration.realGaussianVelocity (OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R j.val)
    let c := fun j : s => φ (h • periodicFrequency j.val)*UnitAddTorus.mFourierCoeff f j.val
    let P := OAI.Analysis.PDE.Concentration.packetSupNorm κ (fun j => (c j).re) (fun j => (c j).im) v
    let ha : 0 < h*L := mul_pos hh (lt_of_lt_of_le zero_lt_one hL)
    Nonempty (PaddedSolutionFamily (n+1) (h*L)
      (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R.toContinuousLinearEquiv))
      (packetPaddedBackground n (h*L) ha (OAI.Analysis.PDE.Concentration.largeBackground (n+1) h))
      (packetPaddedSource R.toContinuousLinearEquiv h (h*L) ha κ
        (fun j => P⁻¹*(c j).re) (fun j => P⁻¹*(c j).im) v (OAI.Analysis.PDE.Concentration.largeBackground (n+1) h))) := by
  dsimp only
  apply nonempty_packetSolutionFamily R.toContinuousLinearEquiv h (h*L) hh
    (mul_pos hh (lt_of_lt_of_le zero_lt_one hL)) _ _ _ _ _ _
    (OAI.Analysis.PDE.Concentration.largeBackground_pos (n+1) hh) packetParameterOne (packetParameterOne_mem_annulus hsmall)
  intro j i
  refine ⟨j.val i,?_⟩
  exact sector_frequency_quantized R j.val
    (sector_frequency_positive R hh j.val (hpos j.val j.property)) i

end OAI.Analysis.Fourier.WavePackets
