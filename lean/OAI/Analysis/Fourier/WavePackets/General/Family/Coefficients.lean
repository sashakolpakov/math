import OAI.Analysis.Fourier.WavePackets.General.Family.Geometry
import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.InverseJets
import OAI.Analysis.PDE.Concentration.Packet.PeriodBasis

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Concentration
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

def LocalDirichletFamily.rawJacobian (G : LocalDirichletFamily D z₀ U)
    (p : Z × E) : E →L[ℝ] E :=
  fderiv ℝ (fun y => G.backward (p.1,y)) (G.forward p)

def LocalDirichletFamily.rawCurvature (G : LocalDirichletFamily D z₀ U)
    (p : Z × E) : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fderiv ℝ (fun y => G.backward (p.1,y))) (G.forward p)

def LocalDirichletFamily.rawBackground (G : LocalDirichletFamily D z₀ U)
    (p : Z × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (D p.1).background) (G.forward p)

def LocalDirichletFamily.rawSource (G : LocalDirichletFamily D z₀ U)
    (p : Z × E) : ℝ := (D p.1).density (G.forward p)

theorem LocalDirichletFamily.rawJacobian_periodic
    (G : LocalDirichletFamily D z₀ U) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => G.rawJacobian (z,x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (range b) := ⟨b i,Submodule.subset_span (mem_range_self i)⟩
  change fderiv ℝ (fun y => G.backward (z,y))
    (G.forward (z,x+e.symm ((l:P),0))) = _
  rw [G.forward_periodic]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.fderiv_equivariant (e.symm ((l:P),0)) (e.symm ((l:P),0))
    (G.backward_periodic z l) _

theorem LocalDirichletFamily.rawCurvature_periodic
    (G : LocalDirichletFamily D z₀ U) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => G.rawCurvature (z,x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (range b) := ⟨b i,Submodule.subset_span (mem_range_self i)⟩
  change fderiv ℝ (fderiv ℝ (fun y => G.backward (z,y)))
    (G.forward (z,x+e.symm ((l:P),0))) = _
  rw [G.forward_periodic]
  apply OAI.Analysis.PDE.Dirichlet.ParameterDeformation.fderiv_equivariant (e.symm ((l:P),0)) (0 : E →L[ℝ] E)
  intro y
  rw [add_zero]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.fderiv_equivariant (e.symm ((l:P),0)) (e.symm ((l:P),0))
    (G.backward_periodic z l) y

theorem LocalDirichletFamily.rawBackground_periodic
    (G : LocalDirichletFamily D z₀ U) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => G.rawBackground (z,x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (range b) := ⟨b i,Submodule.subset_span (mem_range_self i)⟩
  change fderiv ℝ (fderiv ℝ (D z).background)
    (G.forward (z,x+e.symm ((l:P),0))) = _
  rw [G.forward_periodic]
  exact OAI.Analysis.PDE.Dirichlet.latticePeriodic_add_shift e b (D z).background_periodic.fderiv.fderiv _ l

theorem LocalDirichletFamily.rawSource_periodic
    (G : LocalDirichletFamily D z₀ U) (z : Z) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => G.rawSource (z,x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  let l : Submodule.span ℤ (range b) := ⟨b i,Submodule.subset_span (mem_range_self i)⟩
  change (D z).density (G.forward (z,x+e.symm ((l:P),0))) = _
  rw [G.forward_periodic]
  exact OAI.Analysis.PDE.Dirichlet.latticePeriodic_add_shift e b (D z).density_periodic _ l

theorem LocalDirichletFamily.rawJacobian_base
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    G.rawJacobian (z₀,x) = ContinuousLinearMap.id ℝ E := by
  unfold LocalDirichletFamily.rawJacobian
  rw [G.forward_base x (G.source_closed ⟨G.base_mem,hx⟩)]
  exact (G.backward_base_germ hx).fderiv_eq.trans fderiv_id

theorem LocalDirichletFamily.rawCurvature_base
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    G.rawCurvature (z₀,x) = 0 := by
  unfold LocalDirichletFamily.rawCurvature
  rw [G.forward_base x (G.source_closed ⟨G.base_mem,hx⟩)]
  rw [(G.backward_base_germ hx).fderiv.fderiv_eq]
  have he : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_id
  rw [he,fderiv_const_apply]

theorem LocalDirichletFamily.rawBackground_base
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    G.rawBackground (z₀,x) = fderiv ℝ (fderiv ℝ (D z₀).background) x := by
  unfold LocalDirichletFamily.rawBackground
  rw [G.forward_base x (G.source_closed ⟨G.base_mem,hx⟩)]

theorem LocalDirichletFamily.rawSource_base
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    G.rawSource (z₀,x) = (D z₀).density x := by
  unfold LocalDirichletFamily.rawSource
  rw [G.forward_base x (G.source_closed ⟨G.base_mem,hx⟩)]

end OAI.Analysis.Fourier.WavePackets
