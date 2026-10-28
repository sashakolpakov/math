import OAI.Analysis.Fourier.WavePackets.Packet.Fields
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder
open scoped ContDiff

/-- The actual geometric and analytic data at a packet parameter. No
solution, coefficient regularity, or boundedness premise is hidden in this
record's construction from the general Dirichlet theorem. -/
structure PacketInitialization {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (α : ℝ) where
  data : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
  domain : ∀ x, data.defining x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0
  closedDomain : ∀ x, data.defining x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0
  background : data.background = (fun x => packetPaddedBackground n a ha lam (z₀,x))
  source : data.density = (fun x => packetPaddedSource R h a ha κ cR cI v lam (z₀,x))
  solution : PeriodicQuaternionicSolution data
  radius : ℝ
  radius_pos : 0 < radius
  neighborhood : closedBall z₀ radius ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a
  fields : PacketParameterFields R h a ha κ cR cI v lam z₀ data.defining α (ball z₀ radius)
  lifts : OAI.Analysis.PDE.Schauder.LatticeJetLifts (r := data.defining)
    (fun x (hx : data.defining x < 0) => (show data.defining x ≤ 0 from hx.le))
    α (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))

theorem nonempty_packetInitialization (hsolve : FourSlotDirichletExistence)
    {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Nonempty (PacketInitialization R h a ha κ cR cI v lam z₀ α) := by
  obtain ⟨D,hn,hl,hB,hF⟩ := exists_packet_padded_data R h a hh ha κ cR cI v hfreq
    lam hlam z₀ hz₀.1.le hz₀.2.le
  obtain ⟨S⟩ := hsolve (n + 2) ((Fin (n + 2) → ℝ) × (Fin (n + 2) → ℝ))
    (Option (Fin (n + 1)) → ℂ) (Fin (n + 2) ⊕ Fin (n + 2))
    (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) D
  obtain ⟨ρ,hρ,hneigh,⟨C⟩⟩ := exists_packetParameterFields_near R h a hh ha κ cR cI v hfreq
    lam z₀ hz₀ D.defining_smooth.continuous D.defining_periodic hl hα.le hα1
  obtain ⟨J⟩ := OAI.Analysis.PDE.Schauder.nonempty_latticeJetLifts (by omega : 0 < n + 2)
    (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
    D.compact D.defining_smooth D.defining_periodic D.bounded D.regular
    (fun x (hx : D.defining x < 0) => (show D.defining x ≤ 0 from hx.le)) hα hα1
  exact ⟨⟨D,hn,hl,hB,hF,S,ρ,hρ,hneigh,C,J⟩⟩

end OAI.Analysis.Fourier.WavePackets
