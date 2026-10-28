import OAI.Analysis.Fourier.WavePackets.Packet.FlowValues
import OAI.Analysis.Fourier.WavePackets.Packet.FlowBoundary

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace

omit [CompleteSpace T] in
theorem PacketFlowFields.hessianField_eq_packetFlowPushback
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r} (F : PacketFlowFields A D U α)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ U ×ˢ {t : T | ‖t‖ < D.radius}) (w : X) {y : E}
    (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    let x := packetFlowInverse D a z₀ z t y
    let hx := packetFlowInverse_into_domain D a ha z₀ z hz₀ hp.2 hrd hy
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.hessianField J hα ((z,t),w)) ⟨x,hx.le⟩ =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetFlowPushback D a ha lam z₀ z t w) y := by
  dsimp only
  have hx := packetFlowInverse_into_domain D a ha z₀ z hz₀ hp.2 hrd hy
  have he := F.inverse_coefficient_values hz₀ hz hzC hp ⟨_,hx.le⟩ y
    (packetFlowInverse_map D a z₀ z hp.2 y) hy.le
  apply F.analytic.hessianField_eq_local_pushback J hα hr (z,t) w
    (fun y => packetPaddedBackground n a ha lam (z,y)) (packetFlowInverse D a z₀ z t)
    _ y hx
  · exact ((contDiff_packetPaddedBackground n a ha lam).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by norm_num)
  · exact (contDiffAt_packetFlowInverse D a ha z₀ z hz hp.2 hy.le).of_le (by norm_num)
  · rfl
  · exact he.2.2.1
  · exact he.1
  · exact he.2.1

omit [CompleteSpace T] in
theorem PacketFlowFields.packetFlowPushback_equation
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r} (F : PacketFlowFields A D U α)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ U ×ˢ {t : T | ‖t‖ < D.radius}) (w : X)
    (hzero : F.analytic.periodicOperator J hrp hα ((z,t),w) = 0)
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetFlowPushback D a ha lam z₀ z t w) y) =
      packetPaddedSource R h a ha κ cR cI v lam (z,y) := by
  have hx := packetFlowInverse_into_domain D a ha z₀ z hz₀ hp.2 hrd hy
  have he := F.inverse_coefficient_values hz₀ hz hzC hp ⟨_,hx.le⟩ y
    (packetFlowInverse_map D a z₀ z hp.2 y) hy.le
  exact (F.analytic.local_pushback_equation J hα hrp hp w hzero _ _ _ y
    (F.hessianField_eq_packetFlowPushback J hα hr hrd hz₀ hz hzC hp w hy)).trans he.2.2.2

omit [CompleteSpace T] in
theorem PacketFlowFields.packetFlowPushback_positive
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r} (F : PacketFlowFields A D U α)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ U ×ˢ {t : T | ‖t‖ < D.radius}) (w : X)
    (hpos : F.analytic.PositiveAt J hα ((z,t),w))
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetFlowPushback D a ha lam z₀ z t w) y)).PosDef := by
  exact F.analytic.local_pushback_positive J hα (z,t) w hpos _ _ _ y
    (contDiffAt_packetFlowPushback D hr a ha lam z₀ z hz₀ hz hp.2 hrd w hy)
    (F.hessianField_eq_packetFlowPushback J hα hr hrd hz₀ hz hzC hp w hy)

end OAI.Analysis.Fourier.WavePackets
