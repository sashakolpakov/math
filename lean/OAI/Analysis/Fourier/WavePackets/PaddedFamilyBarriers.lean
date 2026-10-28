import OAI.Analysis.Fourier.WavePackets.Dirichlet.MovingBarriers
import OAI.Analysis.Fourier.WavePackets.PaddedTrivialization
import OAI.Analysis.PDE.Concentration.ActualEnergy

noncomputable section
open Set Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4
local notation "P" => (Fin (d+1) → ℝ) × (Fin (d+1) → ℝ)

/-- Locally uniform source barriers for the actual moving physical fibers.
The compact parameter neighborhood, transported quotient closure, and
representative covering are all constructed in the proof. -/
theorem local_uniform_paddedPhysical_barriers
    {b : Basis ι ℝ P} (a : ℝ) (ha : 0 < a) (z₀ : T)
    (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    (D₀ : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b)
    (D : T → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b)
    (hbase : ∀ x, D₀.defining x ≤ 0 ↔ paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (hclosed : ∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a, ∀ x,
      (D z).defining x ≤ 0 ↔ paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0)
    (hA : ContinuousOn (fun p : T × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).background p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0})
    (hR : ContinuousOn (fun p : T × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).defining p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0})
    (hF : ContinuousOn (fun p : T × E => (D p.1).density p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0}) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
      ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ z ∈ closedBall z₀ ρ,
        ∀ S : PeriodicQuaternionicSolution (D z), ∀ x, (D z).defining x ≤ 0 →
          B*(D z).defining x ≤ S.u x ∧ S.u x ≤ c*(D z).defining x := by
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).mem_nhds hz₀)
  have hsub : closedBall z₀ (δ/2) ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a := by
    intro z hz
    apply hδsub
    exact lt_of_le_of_lt (show dist z z₀ ≤ δ/2 from hz) (half_lt_self hδ)
  refine ⟨δ/2,half_pos hδ,hsub,?_⟩
  let Φ : T → E → E := fun z x =>
    paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x
  let Ψ : T → E → E := fun z x =>
    paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) x
  have hΦ : ContinuousOn (fun p : T × E => Φ p.1 p.2)
      (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ {x | D₀.defining x ≤ 0}) := by
    intro p hp
    have hc : ContDiffAt ℝ ∞ (fun q : ℂ × E =>
        paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) q.1 q.2)
        (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2) :=
      contDiffAt_paddedPhysicalTransport_joint d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
        (OAI.Analysis.PDE.Green.energyComplexTime p.1) ha hz₀.1.le ((hbase p.2).mp hp.2)
    have hm : ContDiff ℝ ∞ (fun p : T × E => (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)) :=
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
    have hh := hc.comp p hm.contDiffAt
    have hcomp : ContinuousAt (fun q : T × E =>
        paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2) p := by
      simpa only [Function.comp_def] using hh.continuousAt
    exact hcomp.continuousWithinAt
  apply uniform_barriers_of_closure_transport D₀ D
    (isCompact_closedBall z₀ (δ/2)) hsub Φ Ψ hΦ
  · intro z hz x hx
    apply (hclosed z hz _).mpr
    rw [paddedPhysicalTransport_defining d a _ _ ha hz.1.le ((hbase x).mp hx)]
    exact (hbase x).mp hx
  · intro z hz x hx
    apply (hbase _).mpr
    rw [paddedPhysicalTransport_defining d a _ _ ha hz₀.1.le ((hclosed z hz x).mp hx)]
    exact (hclosed z hz x).mp hx
  · intro z hz x hx
    exact paddedPhysicalTransport_inverse d a _ _ ha hz.1.le hz₀.1.le
      ((hclosed z hz x).mp hx)
  · intro z hz x
    change (paddedPhysicalSplit d (paddedPhysicalTransport d a
      (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) x)).1 = (paddedPhysicalSplit d x).1
    rw [paddedPhysicalTransport_split]
  · exact hA
  · exact hR
  · exact hF

end OAI.Analysis.Fourier.WavePackets
