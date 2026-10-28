import OAI.Analysis.Fourier.WavePackets.FlowParameterFields
import OAI.Analysis.Fourier.WavePackets.Packet.SmoothCoefficients
import OAI.Analysis.Fourier.WavePackets.Packet.BaseData

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

structure PacketFlowFields (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r) (U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)) (α : ℝ) where
  analytic : OAI.Analysis.PDE.Schauder.ParameterJetFields r α (U ×ˢ {t : T | ‖t‖ < D.radius}) e b
  jacobian_value : ∀ p ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.jacobian p) x = flowJacobian D.map A.jacobian (p,x)
  curvature_value : ∀ p ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.curvature p) x = flowCurvature D.map A.jacobian A.curvature (p,x)
  background_value : ∀ p ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.background p) x = flowPullback D.map A.background (p,x)
  source_value : ∀ p ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.source p) x = flowPullback D.map A.source (p,x)

omit [CompleteSpace T] in
theorem nonempty_packetFlowFields
    (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    {K : Set (Option (Fin (n + 1)) → ℂ)} (hK : IsCompact K)
    (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hU : IsOpen U) : Nonempty (PacketFlowFields A D U α) := by
  obtain ⟨F,hJ,hK,hB,hF⟩ := exists_flow_parameterJetFields D hK hr hrp hbounded hα hα1 hU
    A.jacobian A.curvature A.background A.source A.jacobian_smooth A.curvature_smooth
    A.background_smooth A.source_smooth A.jacobian_periodic A.curvature_periodic
    A.background_periodic A.source_periodic
  exact ⟨⟨F,hJ,hK,hB,hF⟩⟩

omit [CompleteSpace T] in
theorem PacketFlowFields.base_values
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r} (F : PacketFlowFields A D U α)
    (hzU : z₀ ∈ U) (hzC : z₀ ∈ C) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    (hrl : ∀ x, r x ≤ 0 → paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (x : {x | r x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.jacobian (z₀,0)) x = ContinuousLinearMap.id ℝ _ ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.curvature (z₀,0)) x = 0 ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.background (z₀,0)) x =
      fderiv ℝ (fderiv ℝ (fun y => packetPaddedBackground n a ha lam (z₀,y))) x ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.source (z₀,0)) x = packetPaddedSource R h a ha κ cR cI v lam (z₀,x) := by
  have hp : (z₀,(0:T)) ∈ U ×ˢ {t : T | ‖t‖ < D.radius} :=
    ⟨hzU,by simpa only [Set.mem_ofPred_eq,norm_zero] using D.radius_pos⟩
  have h := A.exact_germs z₀ hzC x (hrl x x.property)
  refine ⟨?_,?_,?_,?_⟩
  · rw [F.jacobian_value _ hp,flowJacobian_zero D.at_zero,h.1.eq_of_nhds]
    exact packetTransportJ_base (n + 1) a z₀ ha hz₀ (hrl x x.property)
  · rw [F.curvature_value _ hp,flowCurvature_zero D.at_zero,h.2.1.eq_of_nhds]
    exact packetTransportK_base (n + 1) a z₀ ha hz₀ (hrl x x.property)
  · rw [F.background_value _ hp,flowPullback_zero D.at_zero,h.2.2.1.eq_of_nhds]
    rw [pullPhysicalCoefficient_base (n + 1) a z₀ ha hz₀ _ (hrl x x.property)]
    rfl
  · rw [F.source_value _ hp,flowPullback_zero D.at_zero,h.2.2.2.eq_of_nhds]
    exact pullPhysicalCoefficient_base (n + 1) a z₀ ha hz₀ _ (hrl x x.property)

end OAI.Analysis.Fourier.WavePackets
