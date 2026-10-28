import OAI.Analysis.Fourier.WavePackets.PaddedSmoothFamilyBarriers
import OAI.Analysis.Fourier.WavePackets.Packet.BaseData

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- Retain the defining-function germ, in addition to the exact global
packet coefficients, when constructing padded Dirichlet data. -/
theorem exists_packet_padded_barrier_data {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n+1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l : ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (hz' : ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4) :
    ∃ D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit (n+1))
        (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)),
      PaddedPhysicalDataAt a z (packetPaddedBackground n a ha lam)
        (packetPaddedSource R h a ha κ cR cI v lam) D := by
  obtain ⟨D,hn,hl,hg,hB,hF⟩ := exists_packet_fixed_data_exact R h a hh ha κ cR cI v hfreq
    lam hlam z hz hz'
  refine ⟨D.padFourth,⟨?_,?_,?_,?_⟩⟩
  · intro x
    simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth,paddedPhysicalDefining_eq] using
      hl (dropFourth (n+2) x)
  · intro x hx
    have hx' : OAI.Analysis.PDE.Concentration.spatialDefiningFunction (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (dropFourth (n+2) x) ≤ 0 := by
      simpa only [paddedPhysicalDefining_eq] using hx
    have he := (hg _ hx').1.comp_tendsto (dropFourth (n+2)).continuous.continuousAt
    filter_upwards [he] with y hy
    change D.defining (dropFourth (n+2) y) = paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y
    rw [paddedPhysicalDefining_eq]
    exact hy
  · funext x
    change D.background (dropFourth (n+2) x) = _
    rw [hB]
    rfl
  · funext x
    change D.density (dropFourth (n+2) x) = _
    rw [hF]
    rfl

end OAI.Analysis.Fourier.WavePackets
