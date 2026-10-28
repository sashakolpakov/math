import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Family
import OAI.Analysis.Fourier.WavePackets.Packet.Identification

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder
open scoped ContDiff

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

/-- The actual positive implicit branch equals the chosen target solution
after transport to the reference fiber. No continuity of the chosen family
is used in this identification. -/
theorem PaddedSolutionFamily.referenceValue_eq_of_packet_branch
    (S : PaddedSolutionFamily (n + 1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {α : ℝ} {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ (S.data z₀).defining α U)
    {hΩK : {x | (S.data z₀).defining x < 0} ⊆ {x | (S.data z₀).defining x ≤ 0}}
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α (paddedPhysicalSplit (n + 1)) b)
    (hα : 0 ≤ α) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzU : z ∈ U) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    (w : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α)
      (paddedPhysicalSplit (n + 1)) b)
    (hzero : C.analytic.periodicOperator J (S.data z₀).defining_periodic hα (z,w) = 0)
    (hpos : C.analytic.PositiveAt J hα (z,w))
    (x : {x : E | (S.data z₀).defining x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val x = S.referenceValue z₀ (z,x) := by
  have hx : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 :=
    ((S.physical z₀ hz₀).closed x).mp x.property
  let y : E := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
    (OAI.Analysis.PDE.Green.energyComplexTime z) x
  have hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 :=
    (paddedPhysicalTransport_defining (n + 1) a _ _ ha hz.1.le hx).trans_le hx
  have hv := C.packetPushback_identified J hα (S.data z₀).defining_smooth.continuous
    (S.data z₀).defining_periodic (S.physical z₀ hz₀).interior
    (S.physical z₀ hz₀).closed hz₀.1.le hzU hz.1.le w hzero hpos (S.solution z)
    (S.physical z hz).interior (S.physical z hz).closed
    (S.physical z hz).background (S.physical z hz).density
    y (((S.physical z hz).closed y).mpr hy)
  rw [(S.physical z hz).background] at hv
  change packetPaddedBackground n a ha lam (z,y) +
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val)
      (paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y) =
      packetPaddedBackground n a ha lam (z,y) + (S.solution z).u y at hv
  have hinv : paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)
      (OAI.Analysis.PDE.Green.energyComplexTime z₀) y = x :=
    paddedPhysicalTransport_inverse (n + 1) a _ _ ha hz₀.1.le hz.1.le hx
  rw [hinv,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] at hv
  exact add_left_cancel hv

end OAI.Analysis.Fourier.WavePackets
