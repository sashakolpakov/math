import OAI.Analysis.Fourier.WavePackets.Packet.Fields
import OAI.Analysis.PDE.Schauder.Calculus.PhysicalPushback

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Green OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Current

theorem contDiffAt_paddedPhysicalTransport_slice (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4}
    (hx : paddedPhysicalDefining d a τ₀ x ≤ 0) :
    ContDiffAt ℝ ∞ (paddedPhysicalTransport d a τ₀ τ) x := by
  exact (contDiffAt_paddedPhysicalTransport_joint d a τ₀ τ ha ht₀ hx).comp x
    (contDiffAt_const.prodMk contDiffAt_id)

theorem paddedPhysicalTransport_into_domain (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining d a τ₀ x < 0)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hy : paddedPhysicalDefining d a τ y < 0) :
    r (paddedPhysicalTransport d a τ τ₀ y) < 0 := by
  apply (hrd _).mpr
  rw [paddedPhysicalTransport_defining d a τ τ₀ ha ht₀ hy.le]
  exact hy

theorem paddedPhysicalTransport_into_boundary (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (ha : 0 < a) (ht₀ : a ≤ ‖τ₀‖) {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining d a τ₀ x < 0)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining d a τ₀ x ≤ 0)
    {y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4} (hy : paddedPhysicalDefining d a τ y = 0) :
    r (paddedPhysicalTransport d a τ τ₀ y) = 0 := by
  have he := (paddedPhysicalTransport_defining d a τ τ₀ ha ht₀ hy.le).trans hy
  apply le_antisymm ((hrc _).mpr he.le)
  apply le_of_not_gt
  intro hneg
  have := (hrd _).mp hneg
  rw [he] at this
  exact lt_irrefl _ this

variable {n : ℕ} {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α)
  (paddedPhysicalSplit (n + 1)) (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))

def packetPushback (a : ℝ) (ha : 0 < a) (lam : ℝ) (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (v : D) : E → ℝ :=
  OAI.Analysis.PDE.Schauder.physicalPushback (fun y => packetPaddedBackground n a ha lam (z,y))
    (paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀)) v

theorem packetPushback_periodic (a : ℝ) (ha : 0 < a) (lam : ℝ)
    (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (v : D) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (packetPushback a ha lam z₀ z v) := by
  apply OAI.Analysis.PDE.Schauder.latticePeriodic_physicalPushback (packetPaddedBackground_periodic R a ha lam z)
  intro l x
  exact paddedPhysicalTransport_add (n + 1) a _ _ x l

theorem packetPushback_boundary (a : ℝ) (ha : 0 < a) (lam : ℝ)
    (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (v : D) {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0) :
    packetPushback a ha lam z₀ z v y = packetPaddedBackground n a ha lam (z,y) := by
  have hb := paddedPhysicalTransport_into_boundary (n + 1) a
    (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz₀ hrd hrc hy
  unfold packetPushback OAI.Analysis.PDE.Schauder.physicalPushback
  let x := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y
  have hbx : r x = 0 := hb
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val) (show x ∈ {x | r x ≤ 0} from hb.le)]
  have hv := v.property.1 (⟨x,hb.le⟩ : {x | r x ≤ 0})
    (show x ∉ {x | r x < 0} by simpa only [Set.mem_ofPred_eq,hbx] using (not_lt.mpr (le_refl (0 : ℝ))))
  rw [hv,add_zero]

theorem continuousOn_packetPushback (a : ℝ) (ha : 0 < a) (lam : ℝ)
    (z₀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (v : D) : ContinuousOn (packetPushback a ha lam z₀ z v)
      {y | paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0} := by
  have hB : Continuous (fun y : E => packetPaddedBackground n a ha lam (z,y)) :=
    (contDiff_packetPaddedBackground n a ha lam).continuous.comp
      (continuous_const.prodMk continuous_id)
  apply hB.continuousOn.add ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _).comp ?_ ?_)
  · intro y hy
    exact (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz hy).continuousAt.continuousWithinAt
  · intro y hy
    apply (hrc _).mpr
    rw [paddedPhysicalTransport_defining (n + 1) a _ _ ha hz₀ hy]
    exact hy

end OAI.Analysis.Fourier.WavePackets
