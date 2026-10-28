import OAI.Analysis.Fourier.WavePackets.Packet.ParameterFields
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped Topology ContDiff

/-- The exact four-slot data at a parameter value, including the global
coefficient representatives used by the parameter-dependent operator. -/
theorem exists_packet_padded_data {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (hlam : 0 < lam) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (hz₀' : ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖ ≤ 4) :
    ∃ D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit (n + 1))
        (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)),
      (∀ x, D.defining x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0) ∧
      (∀ x, D.defining x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) ∧
      D.background = (fun x => packetPaddedBackground n a ha lam (z₀,x)) ∧
      D.density = (fun x => packetPaddedSource R h a ha κ cR cI v lam (z₀,x)) := by
  obtain ⟨D,hn,hl,_,hB,hF⟩ := exists_packet_fixed_data_exact R h a hh ha κ cR cI v hfreq
    lam hlam z₀ hz₀ hz₀'
  refine ⟨D.padFourth,?_,?_,?_,?_⟩
  · intro x
    simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, paddedPhysicalDefining_eq] using hn (dropFourth (n + 2) x)
  · intro x
    simpa only [OAI.Analysis.Fourier.WavePackets.PeriodicQuaternionicData.padFourth, paddedPhysicalDefining_eq] using hl (dropFourth (n + 2) x)
  · funext x
    change D.background (dropFourth (n + 2) x) = _
    rw [hB]
    rfl
  · funext x
    change D.density (dropFourth (n + 2) x) = _
    rw [hF]
    rfl

theorem packetTransportJ_base (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ha : 0 < a) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    packetTransportJ d a z₀ (z₀,x) = ContinuousLinearMap.id ℝ _ :=
  physicalTransportJ_base d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ hx

theorem packetTransportK_base (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ha : 0 < a) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    packetTransportK d a z₀ (z₀,x) = 0 :=
  physicalTransportK_base d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ hx

theorem pullPhysicalCoefficient_base {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (ha : 0 < a) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → F) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    pullPhysicalCoefficient d a z₀ f (z₀,x) = f (z₀,x) := by
  unfold pullPhysicalCoefficient
  rw [paddedPhysicalTransport_self d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ hx]

theorem paddedPhysicalDefining_nonempty (d : ℕ) (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 | paddedPhysicalDefining d a τ x ≤ 0}.Nonempty := by
  have hq : {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0}.Nonempty := by
    rw [← OAI.Analysis.PDE.Green.physicalFiberInverse_image_closed_ball a τ ha ht]
    exact (OAI.Analysis.Calculus.Current.fiberParameterBall_nonempty d).image _
  obtain ⟨q,hq⟩ := hq
  refine ⟨(paddedPhysicalSplit d).symm (0,q),?_⟩
  change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ
    ((paddedPhysicalSplit d) ((paddedPhysicalSplit d).symm (0,q))).2 ≤ 0
  simpa only [Set.mem_ofPred_eq,ContinuousLinearEquiv.apply_symm_apply] using hq

end OAI.Analysis.Fourier.WavePackets
