import OAI.Analysis.Fourier.WavePackets.General.JointFamily

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U A : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

def dirichletFamilyValue (S : DirichletSolutionFamily D) (p : Z × E) : ℝ := (S p.1).u p.2

theorem LocalDirichletFamily.referenceValue_joint_contDiffAt_self
    (G : LocalDirichletFamily D z₀ U) (S : DirichletSolutionFamily D)
    {x : E} (hx : (D z₀).defining x < 0) :
    ContDiffAt ℝ ∞ (G.referenceValue S) (z₀,x) := by
  let : NeZero m := ⟨by have := (D z₀).dimension; omega⟩
  have hΩK : {y | (D z₀).defining y < 0} ⊆ {y | (D z₀).defining y ≤ 0} :=
    fun y hy => show (D z₀).defining y ≤ 0 from le_of_lt hy
  have hc := G.hasJointGeometricSolutionFamiliesAt (T := E) S
    (α := 1/2) (by norm_num) (by norm_num) hΩK
  exact hc.joint_contDiffAt_interior (D z₀).defining_smooth.continuous
    (D z₀).defining_periodic hx

theorem LocallyTrivialDirichletData.value_joint_contDiffAt_interior
    (hD : LocallyTrivialDirichletData D A) (S : DirichletSolutionFamily D)
    {z : Z} (hz : z ∈ A) {x : E} (hx : (D z).defining x < 0) :
    ContDiffAt ℝ ∞ (dirichletFamilyValue S) (z,x) := by
  obtain ⟨U,hUA,⟨G⟩⟩ := hD.2 z hz
  let H : Z × E → Z × E := fun p => (p.1,G.backward p)
  have hp : (z,x) ∈ G.targetNeighborhood := G.target_closed ⟨G.base_mem,hx.le⟩
  have hH : ContDiffAt ℝ ∞ H (z,x) := contDiffAt_fst.prodMk
    ((G.backward_smooth (z,x) hp).contDiffAt (G.target_open.mem_nhds hp))
  have hHself : H (z,x) = (z,x) := by
    exact Prod.ext rfl (G.backward_base x hp)
  have hs : ContDiffAt ℝ ∞ (G.referenceValue S) (H (z,x)) := by
    rw [hHself]
    exact G.referenceValue_joint_contDiffAt_self S hx
  apply (hs.comp (z,x) hH).congr_of_eventuallyEq
  filter_upwards [G.target_open.mem_nhds hp] with p hpn
  change (S p.1).u p.2 = (S p.1).u (G.forward (p.1,G.backward p))
  rw [G.forward_backward p hpn]

theorem LocalDirichletFamily.referenceValue_joint_contDiffAt_interior
    (G : LocalDirichletFamily D z₀ U) (hD : LocallyTrivialDirichletData D A)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U) (hzA : z ∈ A)
    {x : E} (hx : (D z₀).defining x < 0) :
    ContDiffAt ℝ ∞ (G.referenceValue S) (z,x) := by
  have hp : (z,x) ∈ G.sourceNeighborhood := G.source_closed ⟨hz,hx.le⟩
  have hH : ContDiffAt ℝ ∞ (fun p : Z × E => (p.1,G.forward p)) (z,x) :=
    contDiffAt_fst.prodMk
      ((G.forward_smooth (z,x) hp).contDiffAt (G.source_open.mem_nhds hp))
  exact (hD.value_joint_contDiffAt_interior S hzA (G.forward_strict z hz x hx)).comp (z,x) hH

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem LocallyTrivialDirichletData.isOpen_movingInterior
    (hD : LocallyTrivialDirichletData D A) :
    IsOpen {p : Z × E | p.1 ∈ A ∧ (D p.1).defining p.2 < 0} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨z,x⟩ ⟨hz,hx⟩
  obtain ⟨U,hUA,⟨G⟩⟩ := hD.2 z hz
  have hp : (z,x) ∈ G.targetNeighborhood := G.target_closed ⟨G.base_mem,hx.le⟩
  have hc : ContinuousAt (fun p : Z × E => (D p.1).defining p.2) (z,x) :=
    ((G.defining_smooth (z,x) hp).contDiffAt (G.target_open.mem_nhds hp)).continuousAt
  have hparam : ∀ᶠ p : Z × E in 𝓝 (z,x), p.1 ∈ A :=
    continuous_fst.continuousAt.preimage_mem_nhds (hD.1.mem_nhds hz)
  exact hparam.and (hc.eventually_lt continuousAt_const hx)

theorem LocallyTrivialDirichletData.value_contDiffOn_interior
    (hD : LocallyTrivialDirichletData D A) (S : DirichletSolutionFamily D) :
    ContDiffOn ℝ ∞ (dirichletFamilyValue S) {p : Z × E | p.1 ∈ A ∧ (D p.1).defining p.2 < 0} := by
  intro p hp
  exact (hD.value_joint_contDiffAt_interior S hp.1 hp.2).contDiffWithinAt

end OAI.Analysis.Fourier.WavePackets
