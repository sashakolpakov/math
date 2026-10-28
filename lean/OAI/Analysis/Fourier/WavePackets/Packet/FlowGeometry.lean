import OAI.Analysis.Fourier.WavePackets.FlowInverse
import OAI.Analysis.Fourier.WavePackets.CalculusPacketPushback
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Pushback

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

def packetFlowInverse (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (t : T) : E → E :=
  flowInverse D.map (paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀)) t

def packetFlowPushback (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (t : T) (w : X) : E → ℝ :=
  OAI.Analysis.PDE.Schauder.physicalPushback (fun y => packetPaddedBackground n a ha lam (z,y))
    (packetFlowInverse D a z₀ z t) w

omit [CompleteSpace T] in
theorem packetFlowInverse_map (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) {t : T} (ht : ‖t‖ < D.radius) (y : E) :
    D.map (t,packetFlowInverse D a z₀ z t y) =
      paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y :=
  Function.invFun_eq ((D.bijective t ht).surjective _)

omit [CompleteSpace T] in
theorem packetFlowInverse_into_domain (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {t : T} (ht : ‖t‖ < D.radius)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    r (packetFlowInverse D a z₀ z t y) < 0 := by
  apply (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_preserves_domain (D.bijective t ht) (D.open_domain t ht) _).mpr
  exact paddedPhysicalTransport_into_domain (n + 1) a _ _ ha hz₀ hrd hy

omit [CompleteSpace T] in
theorem packetFlowInverse_into_closed (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {t : T} (ht : ‖t‖ < D.radius)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    r (packetFlowInverse D a z₀ z t y) ≤ 0 := by
  apply (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily_preserves_closed_domain (D.bijective t ht) (D.closed_domain t ht) _).mpr
  apply (hrc _).mpr
  rw [paddedPhysicalTransport_defining (n + 1) a _ _ ha hz₀ hy]
  exact hy

omit [CompleteSpace T] in
theorem contDiffAt_packetFlowInverse (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (a : ℝ) (ha : 0 < a) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) {t : T} (ht : ‖t‖ < D.radius)
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    ContDiffAt ℝ ∞ (packetFlowInverse D a z₀ z t) y := by
  exact (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiff_inverseFamily_slice (U := {s : T | ‖s‖ < D.radius})
    (Φ := D.map) D.inverse_smooth ht).contDiffAt.comp y
    (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz hy)

omit [CompleteSpace T] in
theorem contDiffAt_packetFlowPushback (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    (hr : Continuous r) (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    {t : T} (ht : ‖t‖ < D.radius)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (w : X) {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    ContDiffAt ℝ 2 (packetFlowPushback D a ha lam z₀ z t w) y := by
  apply OAI.Analysis.PDE.Schauder.contDiffAt_physicalPushback_local hr
  · exact ((contDiff_packetPaddedBackground n a ha lam).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by norm_num)
  · exact (contDiffAt_packetFlowInverse D a ha z₀ z hz ht hy.le).of_le (by norm_num)
  · exact packetFlowInverse_into_domain D a ha z₀ z hz₀ ht hrd hy

end OAI.Analysis.Fourier.WavePackets
