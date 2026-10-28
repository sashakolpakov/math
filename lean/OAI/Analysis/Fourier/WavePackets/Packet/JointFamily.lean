import OAI.Analysis.Fourier.WavePackets.Packet.FlowFields
import OAI.Analysis.Fourier.WavePackets.Dirichlet.ParameterFamily
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.FlowIdentification
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.GeometricFamilies
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff Topology

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ}
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace

/-- The independently chosen genuine packet solutions possess actual
combined smooth parameter/spatial-flow families. This supplies the common
neighborhood needed for all mixed orders of boundary regularity. -/
theorem PaddedSolutionFamily.hasJointGeometricSolutionFamiliesAt
    (S : PaddedSolutionFamily (n + 1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hh : 0 < h)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ)*(2*Real.pi)/100)
    {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hΩK : {x | (S.data z₀).defining x < 0} ⊆ {x | (S.data z₀).defining x ≤ 0}) :
    OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := T) e b (S.data z₀).defining
      (S.referenceValue z₀) hΩK α z₀ := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).mem_nhds hz₀)
  have hρ : 0 < δ / 2 := half_pos hδ
  have hclosed : closedBall z₀ (δ / 2) ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a :=
    (closedBall_subset_ball (by linarith)).trans hsub
  obtain ⟨A⟩ := nonempty_packetSmoothCoefficients R h a hh ha κ cR cI v hfreq lam z₀ hz₀.1.le
    (isCompact_closedBall z₀ (δ / 2)) (fun z hz => (hclosed hz).1.le)
  obtain ⟨J⟩ := OAI.Analysis.PDE.Schauder.nonempty_latticeJetLifts (by omega : 0 < n + 2) e b
    (S.data z₀).compact (S.data z₀).defining_smooth (S.data z₀).defining_periodic
    (S.data z₀).bounded (S.data z₀).regular hΩK hα hα1.le
  intro D
  obtain ⟨F⟩ := nonempty_packetFlowFields A D (S.data z₀).compact
    (S.data z₀).defining_smooth.continuous (S.data z₀).defining_periodic
    (S.data z₀).bounded hα.le hα1.le (isOpen_ball (x := z₀) (ε := δ / 2))
  have hp₀ : (z₀,(0:T)) ∈ ball z₀ (δ/2) ×ˢ {t : T | ‖t‖ < D.radius} :=
    ⟨mem_ball_self hρ,by simpa only [norm_zero,Set.mem_ofPred_eq] using D.radius_pos⟩
  have hrl : ∀ x, (S.data z₀).defining x ≤ 0 →
      paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 :=
    fun x hx => ((S.physical z₀ hz₀).closed x).mp hx
  obtain ⟨x,hx⟩ := paddedPhysicalDefining_nonempty (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀.1.le
  let : Nonempty {x | (S.data z₀).defining x ≤ 0} :=
    ⟨⟨x,((S.physical z₀ hz₀).closed x).mpr hx⟩⟩
  have hb := F.base_values (mem_ball_self hρ) (mem_closedBall_self hρ.le) hz₀.1.le hrl
  have hB : ∀ x : {x | (S.data z₀).defining x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.background (z₀,0)) x =
        fderiv ℝ (fderiv ℝ (S.data z₀).background) x := by
    intro x
    rw [(S.physical z₀ hz₀).background]
    exact (hb x).2.2.1
  have hF : ∀ x : {x | (S.data z₀).defining x ≤ 0},
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.source (z₀,0)) x = (S.data z₀).density x := by
    intro x
    rw [(S.physical z₀ hz₀).density]
    exact (hb x).2.2.2
  obtain ⟨w,W,hW,hW₀,hWsub,hw,_,hsolve⟩ := (S.solution z₀).exists_positive_parameter_family
    F.analytic J hα hα1 (isOpen_ball.prod (isOpen_lt continuous_norm continuous_const)) hp₀
    (fun x => (hb x).1) (fun x => (hb x).2.1) hB hF
  let inc := (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  refine ⟨fun p => inc (w p),W,hW,hW₀,inc.contDiff.comp_contDiffOn hw,?_⟩
  filter_upwards [hW.mem_nhds hW₀] with p hp
  intro x
  exact S.referenceValue_eq_of_packet_flow_branch hz₀ F J hα.le
    (hclosed (ball_subset_closedBall (hWsub hp).1))
    (ball_subset_closedBall (hWsub hp).1) (hWsub hp) (w p)
    (hsolve p hp).1 (hsolve p hp).2 x

end OAI.Analysis.Fourier.WavePackets
