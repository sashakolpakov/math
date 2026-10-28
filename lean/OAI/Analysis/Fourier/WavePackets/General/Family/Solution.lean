import OAI.Analysis.Fourier.WavePackets.General.Family.Geometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

/-- Only geometric and data regularity is included here. Existence of
solutions and their joint parameter regularity are not hypotheses. -/
def LocallyTrivialDirichletData
    {s : ℕ} {slots : Fin s → Quaternion ℝ} {e' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V}
    (D : Z → PeriodicQuaternionicData slots e' b) (A : Set Z) : Prop :=
  IsOpen A ∧ ∀ z ∈ A, ∃ U : Set Z, U ⊆ A ∧ Nonempty (LocalDirichletFamily D z U)

abbrev DirichletSolutionFamily {s : ℕ} {slots : Fin s → Quaternion ℝ}
    {e' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V}
    (D : Z → PeriodicQuaternionicData slots e' b) :=
  (z : Z) → PeriodicQuaternionicSolution (D z)

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem nonempty_dirichletSolutionFamily [Nontrivial V]
    (D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    Nonempty (DirichletSolutionFamily D) := by
  classical
  exact ⟨fun z => Classical.choice (D z).nonempty_solution⟩

variable {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}

def LocalDirichletFamily.referenceValue (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) (p : Z × E) : ℝ :=
  (S p.1).u (G.forward p)

theorem LocalDirichletFamily.referenceValue_self (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) {x : E} (hx : (D z₀).defining x ≤ 0) :
    G.referenceValue S (z₀,x) = (S z₀).u x := by
  unfold LocalDirichletFamily.referenceValue
  rw [G.forward_base x (G.source_closed ⟨G.base_mem,hx⟩)]

theorem LocalDirichletFamily.referenceValue_boundary (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U)
    {x : E} (hx : (D z₀).defining x = 0) : G.referenceValue S (z,x) = 0 :=
  (S z).boundary _ (G.forward_boundary hz hx)

theorem LocalDirichletFamily.referenceValue_inverse (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U)
    {y : E} (hy : (D z).defining y ≤ 0) :
    G.referenceValue S (z,G.backward (z,y)) = (S z).u y := by
  unfold LocalDirichletFamily.referenceValue
  rw [G.forward_backward (z,y) (G.target_closed ⟨hz,hy⟩)]

theorem LocalDirichletFamily.referenceValue_periodic (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => G.referenceValue S (z,x)) := by
  intro x l
  rw [OAI.Analysis.PDE.Dirichlet.lattice_translate_eq]
  rw [add_comm (e.symm ((l:P),0)) x]
  change (S z).u (G.forward (z,x+e.symm ((l:P),0))) = _
  rw [G.forward_periodic]
  exact OAI.Analysis.PDE.Dirichlet.latticePeriodic_add_shift e b (S z).periodic _ l

theorem LocalDirichletFamily.forward_slice_contDiffAt (G : LocalDirichletFamily D z₀ U)
    {z : Z} (hz : z ∈ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    ContDiffAt ℝ ∞ (fun y => G.forward (z,y)) x := by
  have hp : (z,x) ∈ G.sourceNeighborhood := G.source_closed ⟨hz,hx⟩
  exact ((G.forward_smooth (z,x) hp).contDiffAt (G.source_open.mem_nhds hp)).comp x
    (contDiffAt_const.prodMk contDiffAt_id)

theorem LocalDirichletFamily.backward_slice_contDiffAt (G : LocalDirichletFamily D z₀ U)
    {z : Z} (hz : z ∈ U) {y : E} (hy : (D z).defining y ≤ 0) :
    ContDiffAt ℝ ∞ (fun x => G.backward (z,x)) y := by
  have hp : (z,y) ∈ G.targetNeighborhood := G.target_closed ⟨hz,hy⟩
  exact ((G.backward_smooth (z,y) hp).contDiffAt (G.target_open.mem_nhds hp)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

theorem LocalDirichletFamily.referenceValue_slice_contDiffAt (G : LocalDirichletFamily D z₀ U)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U)
    {x : E} (hx : (D z₀).defining x ≤ 0) :
    ContDiffAt ℝ ∞ (fun y => G.referenceValue S (z,y)) x :=
  (S z).smooth.contDiffAt.comp x (G.forward_slice_contDiffAt hz hx)

end OAI.Analysis.Fourier.WavePackets
