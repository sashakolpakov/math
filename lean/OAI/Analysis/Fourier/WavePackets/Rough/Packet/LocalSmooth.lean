import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Boundary
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.SmoothGluing

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n+1) → ℝ} {lam : ℝ}
local notation "PT" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "PE" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4
local notation "b" => paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

/-- Local joint smoothness of the actual chosen family, including its
moving spatial boundary. No regularity premise on that family remains. -/
theorem PaddedSolutionFamily.local_smooth_representative
    (S : PaddedSolutionFamily (n+1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hh : 0 < h)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
    {z₀ : PT} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x₀ : PE}
    (hx₀ : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x₀ ≤ 0) :
    ∃ O : Set (PT × PE), IsOpen O ∧ (z₀,x₀) ∈ O ∧
      ∃ g : PT × PE → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∀ p ∈ O, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
          paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
          g p = S.physicalValue p := by
  rcases hx₀.lt_or_eq with hx | hx
  · exact S.local_physical_interior_representative hh hfreq hz₀ hx
  · exact S.local_physical_boundary_representative hh hfreq hz₀ hx

/-- One globally spatially periodic representative is jointly smooth on
the entire open parameter annulus and equals the genuine solutions on
every closed moving fiber. No extension across the annulus endpoints is
claimed or needed. -/
theorem PaddedSolutionFamily.exists_joint_smooth_representative
    (S : PaddedSolutionFamily (n+1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hh : 0 < h)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100) :
    ∃ u : PT × PE → ℝ,
      ContDiffOn ℝ ∞ u (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ univ) ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n+1)) b (fun x => u (z,x))) ∧
      ∀ p, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
        paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
        u p = S.physicalValue p := by
  exact S.smooth_representative_on_annulus ha
    (fun p hp hx => S.local_smooth_representative hh hfreq hp hx)

end OAI.Analysis.Fourier.WavePackets
