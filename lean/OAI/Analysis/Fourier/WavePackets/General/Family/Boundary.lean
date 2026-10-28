import OAI.Analysis.Fourier.WavePackets.General.Family.Interior
import OAI.Analysis.Fourier.WavePackets.General.Family.Symbol
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.PhysicalChart
import OAI.Analysis.PDE.Elliptic.Calculus.JointBoundaryChart

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U A : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
local notation "X" => EuclideanSpace ℝ (Fin (m*4))

/-- Joint smoothness up to a reference boundary for an arbitrary smooth
moving family. Every analytic input is derived from the original data,
the actual Dirichlet solutions, and the local closure diffeomorphisms. -/
theorem LocalDirichletFamily.referenceValue_local_boundary
    (G : LocalDirichletFamily D z₀ U) (hUA : U ⊆ A)
    (hD : LocallyTrivialDirichletData D A) (S : DirichletSolutionFamily D)
    {x₀ : E} (hx₀ : (D z₀).defining x₀ = 0) :
    ∃ O : Set (Z × E), IsOpen O ∧ (z₀,x₀) ∈ O ∧
      ∃ g : Z × E → ℝ, ContDiff ℝ ∞ g ∧
        ∀ p ∈ O, (D z₀).defining p.2 ≤ 0 → g p = G.referenceValue S p := by
  have hm := (D z₀).dimension
  let : NeZero m := ⟨by omega⟩
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (G.open_parameter.mem_nhds G.base_mem)
  let ρ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hC : closedBall z₀ ρ ⊆ U :=
    (closedBall_subset_ball (show ρ < δ by dsimp [ρ]; linarith)).trans hδsub
  obtain ⟨B⟩ := G.nonempty_smoothFamilyCoefficients (isCompact_closedBall z₀ ρ) hC
  let j : X ≃ₗᵢ[ℝ] E := (OAI.Analysis.PDE.Dirichlet.flattenFourSlots m).symm
  let k : Fin (m*4) := ⟨0,by omega⟩
  obtain ⟨c,Φ,Ψ,hc,hΦ,hΨ,hΦ0,hΨ0,hchart,V₀,hV₀,hxV₀,hΦΨV₀,hΨV₀⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_joint_boundary_chart j k (D z₀).defining_smooth x₀ hx₀
      ((D z₀).regular x₀ hx₀)
  let hΩK : {x : E | (D z₀).defining x < 0} ⊆ {x | (D z₀).defining x ≤ 0} :=
    fun x hx => show (D z₀).defining x ≤ 0 from le_of_lt hx
  have hbase : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := E) e b (D z₀).defining
      (G.referenceValue S) hΩK (1/2) z₀ :=
    G.hasJointGeometricSolutionFamiliesAt S (by norm_num) (by norm_num) hΩK
  have htangent : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt
      (T := (EuclideanSpace.proj k : X →L[ℝ] ℝ).ker) e b (D z₀).defining
      (G.referenceValue S) hΩK (1/2) z₀ :=
    G.hasJointGeometricSolutionFamiliesAt S (by norm_num) (by norm_num) hΩK
  apply OAI.Analysis.PDE.Dirichlet.ParameterDeformation.exists_smooth_joint_physical_chart e b (D z₀).defining
    (D z₀).defining_smooth (D z₀).defining_periodic (D z₀).regular
    (D z₀).closed_subset_closure hΩK (1/2) (G.referenceValue S)
    isOpen_ball (mem_ball_self hρ) hbase
    (fun z hz x hx => G.referenceValue_joint_contDiffAt_interior hD S
      (hC (ball_subset_closedBall hz)) (hUA (hC (ball_subset_closedBall hz))) hx)
    j Φ Ψ hΦ hΨ (EuclideanSpace.proj k) (EuclideanSpace.single k 1) (by simp)
    hc (fun x hx => (hchart x hx).2.2) (fun x hx => (hchart x hx).1)
    (fun x hx => (hchart x hx).2.1) htangent
    (fun z hz x hx => (G.referenceValue_slice_contDiffAt S
      (hC (ball_subset_closedBall hz)) hx).of_le (by simp))
    B.background B.jacobian B.curvature B.source
    B.background_smooth B.jacobian_smooth B.curvature_smooth B.source_smooth
    (fun z hz x hx => B.jacobian_surjective (hC (ball_subset_closedBall hz))
      (ball_subset_closedBall hz) hx)
    (fun z hz x hx => B.referenceValue_positive S (hC (ball_subset_closedBall hz))
      (ball_subset_closedBall hz) hx)
    (fun z hz x hx => B.referenceValue_equation S (hC (ball_subset_closedBall hz))
      (ball_subset_closedBall hz) hx)
    hΨ0 hV₀ hxV₀ hΦΨV₀ hΨV₀

end OAI.Analysis.Fourier.WavePackets
