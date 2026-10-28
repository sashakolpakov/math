import OAI.Analysis.Fourier.WavePackets.PaddedFamilyBarriers
import OAI.Analysis.Fourier.WavePackets.FamilyHessianContinuity

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green
open scoped Topology ContDiff Matrix.Norms.Elementwise

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d+1) 4
local notation "P" => (Fin (d+1) → ℝ) × (Fin (d+1) → ℝ)

/-- Exact data describing the physical closed fiber. The defining function
may be any smooth global extension of the literal rational germ. -/
structure PaddedPhysicalDataAt {b : Basis ι ℝ P} (a : ℝ) (z : T)
    (B F : T × E → ℝ)
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b) : Prop where
  closed : ∀ x, D.defining x ≤ 0 ↔ paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0
  defining_germ : ∀ x, paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
    D.defining =ᶠ[𝓝 x] paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z)
  background : D.background = fun x => B (z,x)
  density : D.density = fun x => F (z,x)

/-- Actual smooth coefficients and physical defining germs yield locally
uniform barriers without any assumed family-Hessian continuity or compact
covering data. -/
theorem local_uniform_paddedPhysical_barriers_of_smooth_data
    {b : Basis ι ℝ P} (a : ℝ) (ha : 0 < a) (z₀ : T)
    (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    (B F : T × E → ℝ) (hB : ContDiff ℝ ∞ B) (hF : ContDiff ℝ ∞ F)
    (D : T → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b)
    (hD : ∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a, PaddedPhysicalDataAt a z B F (D z)) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
      ∃ b₁ b₀ : ℝ, 0 < b₀ ∧ b₀ ≤ b₁ ∧ ∀ z ∈ closedBall z₀ ρ,
        ∀ S : PeriodicQuaternionicSolution (D z), ∀ x,
          paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
          b₁*paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ S.u x ∧
          S.u x ≤ b₀*paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x := by
  have hA : ContinuousOn (fun p : T × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).background p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0} := by
    apply continuousOn_family_quaternionHessian_of_germs (Z := T) (m := d+1)
      (s := 4) OAI.Analysis.Calculus.Quaternion.fourSlots (f := B) (g := fun z => (D z).background)
      (fun _ _ => hB.contDiffAt)
    intro p hp
    rw [(hD p.1 hp.1).background]
  have hR : ContinuousOn (fun p : T × E => OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (D p.1).defining p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0} := by
    apply continuousOn_family_quaternionHessian_of_germs (Z := T) (m := d+1)
      (s := 4) OAI.Analysis.Calculus.Quaternion.fourSlots (g := fun z => (D z).defining)
      (f := fun p => paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2)
    · intro p hp
      exact contDiffAt_paddedPhysicalDefining_joint d a ha p hp.1.1.le
        (((hD p.1 hp.1).closed p.2).mp hp.2)
    · intro p hp
      exact (hD p.1 hp.1).defining_germ p.2 (((hD p.1 hp.1).closed p.2).mp hp.2)
  have hFc : ContinuousOn (fun p : T × E => (D p.1).density p.2)
      {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧ (D p.1).defining p.2 ≤ 0} := by
    apply hF.continuous.continuousOn.congr
    intro p hp
    change (D p.1).density p.2 = F p
    rw [(hD p.1 hp.1).density]
  obtain ⟨ρ,hρ,hρsub,b₁,b₀,hb₀,hb,hbound⟩ :=
    local_uniform_paddedPhysical_barriers a ha z₀ hz₀ (D z₀) D
      (hD z₀ hz₀).closed (fun z hz => (hD z hz).closed) hA hR hFc
  refine ⟨ρ,hρ,hρsub,b₁,b₀,hb₀,hb,?_⟩
  intro z hz S x hx
  have hr := ((hD z (hρsub hz)).defining_germ x hx).eq_of_nhds
  simpa only [hr] using hbound z hz S x (((hD z (hρsub hz)).closed x).mpr hx)

end OAI.Analysis.Fourier.WavePackets
