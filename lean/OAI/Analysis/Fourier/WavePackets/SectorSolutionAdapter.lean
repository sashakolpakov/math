import OAI.Analysis.Fourier.WavePackets.SectorPacketParameters

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology

/-- The final finite-sector specialization of a physical packet solver.
The input coefficients are arbitrary; normalization by the packet norm
does not require that norm to be nonzero. -/
theorem nonempty_sector_solution_of_physical {n : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1)) (h L : ℝ)
    (hh : 0 < h)
    (s : Finset (Fin (n+2) → ℤ)) (φ : Space (n+2) → ℂ)
    (hpos : ∀ k ∈ s, 0 < OAI.Analysis.PDE.Concentration.gaussianFrequencyK (h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency R k))
    (f : UnitAddTorus (Fin (n+2)) → ℂ)
    (hsolve : ∀ (κ cR cI : s → ℝ) (v : s → Fin (n+1) → ℝ),
      (∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
        (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100) →
      Nonempty (OAI.Analysis.PDE.Concentration.PhysicalPacketSolution R.toContinuousLinearEquiv h (h*L) κ cR cI v
        (OAI.Analysis.PDE.Concentration.largeBackground (n+1) h))) :
    Nonempty (OAI.Analysis.PDE.Concentration.SectorPolynomialSolution R h L s φ f) := by
  dsimp only [OAI.Analysis.PDE.Concentration.SectorPolynomialSolution]
  apply hsolve
  intro j i
  refine ⟨j.val i,?_⟩
  exact sector_frequency_quantized R j.val
    (sector_frequency_positive R hh j.val (hpos j.val j.property)) i

end OAI.Analysis.Fourier.WavePackets
