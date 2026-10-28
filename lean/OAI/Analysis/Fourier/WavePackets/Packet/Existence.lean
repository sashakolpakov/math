import OAI.Analysis.Fourier.WavePackets.Packet.Initialization
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Existence

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder
open scoped ContDiff

/-- The literal packet initialization now follows from the proved general
periodic quaternionic Dirichlet theorem, with no solvability premise. -/
theorem nonempty_packetInitialization_unconditional
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Nonempty (PacketInitialization R h a ha κ cR cI v lam z₀ α) :=
  nonempty_packetInitialization fourSlotDirichletExistence R h a hh ha κ cR cI v hfreq
    lam hlam z₀ hz₀ hα hα1

end OAI.Analysis.Fourier.WavePackets
