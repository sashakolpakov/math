import OAI.Analysis.Fourier.WavePackets.Packet.FlowGeometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

omit [CompleteSpace T] in
theorem packetFlowPushback_periodic (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    {t : T} (ht : ‖t‖ < D.radius) (w : X) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (packetFlowPushback D a ha lam z₀ z t w) := by
  apply OAI.Analysis.PDE.Schauder.latticePeriodic_physicalPushback (packetPaddedBackground_periodic R a ha lam z)
  intro l x
  change OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily D.map t
    (paddedPhysicalTransport (n + 1) a _ _ (x + (paddedPhysicalSplit (n + 1)).symm (l,0))) = _
  rw [paddedPhysicalTransport_add]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_equivariant t (D.bijective t ht)
    ((paddedPhysicalSplit (n + 1)).symm (l,0)) (D.equivariant t l) _

omit [CompleteSpace T] in
theorem packetFlowPushback_boundary (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {t : T} (ht : ‖t‖ < D.radius)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (w : X) {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0) :
    packetFlowPushback D a ha lam z₀ z t w y = packetPaddedBackground n a ha lam (z,y) := by
  let x := packetFlowInverse D a z₀ z t y
  have hx : r x ≤ 0 := packetFlowInverse_into_closed D a ha z₀ z hz₀ ht hrc hy.le
  have hn : ¬ r x < 0 := by
    intro hn
    have hm := (D.open_domain t ht x).mpr hn
    rw [packetFlowInverse_map D a z₀ z ht y] at hm
    have hb := paddedPhysicalTransport_into_boundary (n + 1) a
      (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz₀ hrd hrc hy
    linarith
  unfold packetFlowPushback OAI.Analysis.PDE.Schauder.physicalPushback
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val) (show x ∈ {x | r x ≤ 0} from hx)]
  have hw := w.property.1 (⟨x,hx⟩ : {x | r x ≤ 0}) hn
  rw [hw,add_zero]

omit [CompleteSpace T] in
theorem continuousOn_packetFlowPushback (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    {t : T} (ht : ‖t‖ < D.radius)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (w : X) : ContinuousOn (packetFlowPushback D a ha lam z₀ z t w)
      {y | paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0} := by
  have hB : Continuous (fun y : E => packetPaddedBackground n a ha lam (z,y)) :=
    (contDiff_packetPaddedBackground n a ha lam).continuous.comp
      (continuous_const.prodMk continuous_id)
  apply hB.continuousOn.add ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _).comp ?_ ?_)
  · intro y hy
    exact (contDiffAt_packetFlowInverse D a ha z₀ z hz ht hy).continuousAt.continuousWithinAt
  · intro y hy
    exact packetFlowInverse_into_closed D a ha z₀ z hz₀ ht hrc hy

end OAI.Analysis.Fourier.WavePackets
