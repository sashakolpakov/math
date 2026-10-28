import OAI.Analysis.Fourier.WavePackets.Rough.Packet.SmoothGluing
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.GluedSolution

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology

/-- The local joint regularity of the actual Dirichlet family glues and
descends to one physical packet potential. The local representatives need
not agree away from the moving closed domains. -/
theorem PaddedSolutionFamily.nonempty_physicalPacketSolution_of_local_smooth
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : ι → ℝ) (v : ι → Fin (n+1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam)
    (S : PaddedSolutionFamily (n+1) a
      (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hl : ∀ p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4,
      p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
      paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
      ∃ O : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4), IsOpen O ∧ p ∈ O ∧
        ∃ u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4 → ℝ, ContDiffOn ℝ ∞ u O ∧
          ∀ q ∈ O, q.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
            paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2 ≤ 0 →
            u q = S.physicalValue q) :
    Nonempty (OAI.Analysis.PDE.Concentration.PhysicalPacketSolution R h a κ cR cI v lam) := by
  obtain ⟨g,hg,hp,he⟩ := S.smooth_representative_on_annulus ha hl
  obtain ⟨P,_⟩ := S.exists_physicalPacketSolution_of_gluing R h a hh ha κ cR cI v
    hfreq lam hlam g hg hp (fun z hz x hx => he (z,x) hz hx)
  exact ⟨P⟩

end OAI.Analysis.Fourier.WavePackets
