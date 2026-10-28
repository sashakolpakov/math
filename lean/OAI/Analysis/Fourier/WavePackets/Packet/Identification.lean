import OAI.Analysis.Fourier.WavePackets.CalculusPacketPushback
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore
open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

/-- Fiberwise uniqueness identifies the actual moving-fiber pushback of
the Banach branch with every classical target solution. -/
theorem PacketParameterFields.packetPushback_identified
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hrc : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzU : z ∈ U) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (w : X)
    (hzero : C.analytic.periodicOperator J hrp hα (z,w) = 0)
    (hpos : C.analytic.PositiveAt J hα (z,w))
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
    (S : PeriodicQuaternionicSolution D)
    (hDd : ∀ y, D.defining y < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0)
    (hDc : ∀ y, D.defining y ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0)
    (hB : D.background = fun y => packetPaddedBackground n a ha lam (z,y))
    (hF : D.density = fun y => packetPaddedSource R h a ha κ cR cI v lam (z,y)) :
    ∀ y, D.defining y ≤ 0 →
      packetPushback a ha lam z₀ z w y = D.background y + S.u y := by
  have hu : ContDiffOn ℝ 2 (packetPushback a ha lam z₀ z w) {y | D.defining y < 0} := by
    intro y hy
    exact (contDiffAt_packetPushback hr hrd hz₀ z hz w ((hDd y).mp hy)).contDiffWithinAt
  have huc : ContinuousOn (packetPushback a ha lam z₀ z w) {y | D.defining y ≤ 0} :=
    (continuousOn_packetPushback a ha lam z₀ z hz₀ hz hrc w).mono
      (fun y hy => (hDc y).mp hy)
  have hp : ∀ y, D.defining y < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetPushback a ha lam z₀ z w) y)).PosDef :=
    fun y hy => C.packetPushback_positive J hα hr hrd hz₀ hzU hz w hpos ((hDd y).mp hy)
  have he : ∀ y, D.defining y < 0 →
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetPushback a ha lam z₀ z w) y) = D.density y := by
    intro y hy
    rw [hF]
    exact C.packetPushback_equation J hα hr hrp hrd hz₀ hzU hz w hzero ((hDd y).mp hy)
  apply OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice D.dimension e b D.compact
    hu ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffOn
    (D.defining_smooth.of_le (by simp)) huc
    (D.background_smooth.add S.smooth).continuous.continuousOn D.bounded
    D.defining_periodic (packetPushback_periodic a ha lam z₀ z w)
    (D.background_periodic.add S.periodic)
    (fun y hy => D.defining_positive y hy.le) hp S.admissible
    (fun y hy => (he y hy).trans (S.equation y hy).symm)
  intro y hy
  have hphy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y = 0 := by
    refine le_antisymm ((hDc y).mp hy.le) (le_of_not_gt ?_)
    intro hn
    have hdy := (hDd y).mpr hn
    linarith
  rw [packetPushback_boundary a ha lam z₀ z hz₀ hrd hrc w hphy,S.boundary y hy,add_zero,hB]

end OAI.Analysis.Fourier.WavePackets
