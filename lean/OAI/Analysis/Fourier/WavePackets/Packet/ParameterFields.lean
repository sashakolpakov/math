import OAI.Analysis.Fourier.WavePackets.Packet.CoefficientExtensions
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.JetFields

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped Topology ContDiff

/-- Actual Hölder-valued coefficient fields for the moving packet fiber.
All four fields are constructed from the physical formulas, not supplied as
regularity assumptions. The spatial defining extension only fixes the
representation of the already specified closed base fiber. -/
theorem exists_packet_parameterJetFields {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ} (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) r)
    (hrl : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {U T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hU : IsOpen U) (hT : IsCompact T) (hUT : U ⊆ T)
    (hTreg : ∀ z ∈ T, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    ∃ C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U (paddedPhysicalSplit (n + 1))
        (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)),
      (∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) x =
        packetTransportJ (n + 1) a z₀ (z,x)) ∧
      (∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) x =
        packetTransportK (n + 1) a z₀ (z,x)) ∧
      (∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x =
        pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedBackgroundHessian n a ha lam) (z,x)) ∧
      (∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x =
        pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedSource R h a ha κ cR cI v lam) (z,x)) := by
  obtain ⟨J,K,hJ,hK,hJp,hKp,heJK⟩ := exists_packetTransport_extensions (n + 1) a z₀ ha hz₀
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) hT hTreg
  obtain ⟨B,F,hB,hF,hBp,hFp,heBF⟩ := exists_packet_data_extensions R h a hh ha κ cR cI v hfreq lam z₀ hz₀ hT
  have hcompact := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel (d := n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ 0 (by norm_num)
  have hbounded (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4) (hx : r x ≤ 0) :
      (paddedPhysicalSplit (n + 1) x).2 ∈
        {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) q ≤ 0} := (hrl x).mp hx
  obtain ⟨C,hCJ,hCK,hCB,hCF⟩ := OAI.Analysis.PDE.Schauder.exists_parameterJetFields
    (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
    hcompact hr hrp hbounded hα hα1 hU J K B F hJ.contDiffOn hK.contDiffOn hB.contDiffOn hF.contDiffOn
    (fun z _ => hJp z) (fun z _ => hKp z) (fun z _ => hBp z) (fun z _ => hFp z)
  refine ⟨C,?_,?_,?_,?_⟩
  · intro z hz x
    exact (hCJ z hz x).trans (heJK z (hUT hz) x ((hrl x).mp x.property)).1.eq_of_nhds
  · intro z hz x
    exact (hCK z hz x).trans (heJK z (hUT hz) x ((hrl x).mp x.property)).2.eq_of_nhds
  · intro z hz x
    exact (hCB z hz x).trans (heBF z (hUT hz) x ((hrl x).mp x.property)).1.eq_of_nhds
  · intro z hz x
    exact (hCF z hz x).trans (heBF z (hUT hz) x ((hrl x).mp x.property)).2.eq_of_nhds

end OAI.Analysis.Fourier.WavePackets
