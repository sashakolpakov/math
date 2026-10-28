import OAI.Analysis.Fourier.WavePackets.SectorSolutionAdapter
import OAI.Analysis.Fourier.WavePackets.Packet.SmoothAssembly
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.LocalSmooth

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology

/-- Actual smooth physical packet potentials for arbitrary lattice-quantized
finite coefficients. Existence, joint regularity, periodicity and the
nonlinear equation are all inherited from the constructed Dirichlet family. -/
theorem nonempty_physicalPacketSolution
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (hsmall : a ≤ 1/4)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n+1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam) :
    Nonempty (OAI.Analysis.PDE.Concentration.PhysicalPacketSolution R h a κ cR cI v lam) := by
  obtain ⟨S⟩ := nonempty_packetSolutionFamily R h a hh ha κ cR cI v hfreq lam hlam
    packetParameterOne (packetParameterOne_mem_annulus hsmall)
  apply S.nonempty_physicalPacketSolution_of_local_smooth R h a hh ha κ cR cI v
    hfreq lam hlam
  intro p hp hx
  exact S.local_smooth_representative hh hfreq hp hx

/-- The source's finite positive-frequency packet solvability requirement,
with no existence or regularity premise. -/
theorem positive_packet_solvability (n : ℕ) : PositivePacketSolvability n := by
  intro R h L hh hL hsmall s φ hpos f
  apply nonempty_sector_solution_of_physical R h L hh s φ hpos f
  intro κ cR cI v hfreq
  exact nonempty_physicalPacketSolution R.toContinuousLinearEquiv h (h*L) hh
    (mul_pos hh (lt_of_lt_of_le zero_lt_one hL)) hsmall κ cR cI v hfreq
    (OAI.Analysis.PDE.Concentration.largeBackground (n+1) h) (OAI.Analysis.PDE.Concentration.largeBackground_pos (n+1) hh)

end OAI.Analysis.Fourier.WavePackets
