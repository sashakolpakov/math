import OAI.Analysis.Fourier.WavePackets.General.Family.Geometry
import OAI.Analysis.Fourier.WavePackets.Dirichlet.MovingBarriers
import OAI.Analysis.Fourier.WavePackets.FamilyHessianContinuity

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff Matrix.Norms.Elementwise

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

/-- Jointly smooth local data give uniform barriers on every compact set of
parameters. The compact physical representatives and Hessian continuity are
derived from the family, rather than assumed separately. -/
theorem LocalDirichletFamily.uniform_barriers_on_compact
    (G : LocalDirichletFamily D z₀ U) {L : Set Z}
    (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ B c : ℝ, 0 < c ∧ c ≤ B ∧ ∀ z ∈ L,
      ∀ S : PeriodicQuaternionicSolution (D z), ∀ x,
      (D z).defining x ≤ 0 →
      B * (D z).defining x ≤ S.u x ∧ S.u x ≤ c * (D z).defining x := by
  apply uniform_barriers_of_closure_transport (D z₀) D hL hLU
    (fun z x => G.forward (z,x)) (fun z x => G.backward (z,x))
  · exact G.forward_smooth.continuousOn.mono G.source_closed
  · exact G.forward_closed
  · exact G.backward_closed
  · intro z hz x hx
    exact G.forward_backward (z,x) (G.target_closed ⟨hz,hx⟩)
  · exact G.backward_first
  · intro p hp
    exact (contDiffAt_family_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      ((G.background_smooth p (G.target_closed hp)).contDiffAt
        (G.target_open.mem_nhds (G.target_closed hp)))).continuousAt.continuousWithinAt
  · intro p hp
    exact (contDiffAt_family_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
      ((G.defining_smooth p (G.target_closed hp)).contDiffAt
        (G.target_open.mem_nhds (G.target_closed hp)))).continuousAt.continuousWithinAt
  · exact G.density_smooth.continuousOn.mono G.target_closed

/-- In finite-dimensional parameter spaces the barriers can be chosen
uniformly on a closed neighborhood of the base parameter. -/
theorem LocalDirichletFamily.locally_uniform_barriers
    [FiniteDimensional ℝ Z] (G : LocalDirichletFamily D z₀ U) :
    ∃ r B c : ℝ, 0 < r ∧ Metric.closedBall z₀ r ⊆ U ∧
      0 < c ∧ c ≤ B ∧ ∀ z ∈ Metric.closedBall z₀ r,
      ∀ S : PeriodicQuaternionicSolution (D z), ∀ x,
      (D z).defining x ≤ 0 →
      B * (D z).defining x ≤ S.u x ∧ S.u x ≤ c * (D z).defining x := by
  obtain ⟨r,hr,hU⟩ := Metric.mem_nhds_iff.mp (G.open_parameter.mem_nhds G.base_mem)
  have hsub : Metric.closedBall z₀ (r/2) ⊆ U := by
    intro z hz
    apply hU
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by linarith))
  obtain ⟨B,c,hc,hcB,hbar⟩ :=
    G.uniform_barriers_on_compact (isCompact_closedBall z₀ (r/2)) hsub
  exact ⟨r/2,B,c,by positivity,hsub,hc,hcB,hbar⟩

end OAI.Analysis.Fourier.WavePackets
