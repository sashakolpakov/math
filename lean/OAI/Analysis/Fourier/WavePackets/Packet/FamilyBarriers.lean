import OAI.Analysis.Fourier.WavePackets.Packet.BarrierData

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- The literal packet coefficients admit a family of valid Dirichlet data
with locally uniform barriers on the actual moving fibers. Every compact
cover, continuity statement, and barrier constant is derived internally. -/
theorem exists_packet_family_with_locally_uniform_barriers {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n+1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l : ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam) (zbase : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hzbase : zbase ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    ∃ D : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit (n+1))
        (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)),
      (∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a,
        PaddedPhysicalDataAt a z (packetPaddedBackground n a ha lam)
          (packetPaddedSource R h a ha κ cR cI v lam) (D z)) ∧
      ∀ z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a,
        ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
          ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ z ∈ closedBall z₀ ρ,
            ∀ S : PeriodicQuaternionicSolution (D z), ∀ x,
              paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
              B*paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ S.u x ∧
              S.u x ≤ c*paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x := by
  classical
  obtain ⟨D₀,hD₀⟩ := exists_packet_padded_barrier_data R h a hh ha κ cR cI v hfreq
    lam hlam zbase hzbase.1.le hzbase.2.le
  have hex : ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3,
      ∃ D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit (n+1))
        (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)),
        z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a → PaddedPhysicalDataAt a z
          (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam) D := by
    intro z
    by_cases hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a
    · obtain ⟨D,hD⟩ := exists_packet_padded_barrier_data R h a hh ha κ cR cI v hfreq
        lam hlam z hz.1.le hz.2.le
      exact ⟨D,fun _ => hD⟩
    · exact ⟨D₀,fun h => (hz h).elim⟩
  choose D hD using hex
  refine ⟨D,hD,?_⟩
  intro z₀ hz₀
  exact local_uniform_paddedPhysical_barriers_of_smooth_data a ha z₀ hz₀
    (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam)
    (contDiff_packetPaddedBackground n a ha lam)
    (contDiff_packetPaddedSource R h a hh ha κ cR cI v lam) D hD

end OAI.Analysis.Fourier.WavePackets
