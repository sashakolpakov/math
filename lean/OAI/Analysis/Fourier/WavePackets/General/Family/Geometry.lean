import OAI.Analysis.Fourier.WavePackets.Dirichlet.Existence
import OAI.Analysis.Fourier.WavePackets.ParameterExtension

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z P V ι : Type*} {m s : ℕ} {slots : Fin s → Quaternion ℝ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s

/-- A genuine smooth local trivialization of a family of closed periodic
Dirichlet domains. The maps and data are only required to be jointly smooth
on open neighborhoods of the closed fibers. In particular this does not
require a smooth extension across an endpoint of the parameter domain.

The defining functions are independent of the periodic coordinates, as in
the manuscript. The charts preserve these coordinates; their inverses are
actual inverses on open neighborhoods, not merely on the boundary. -/
structure LocalDirichletFamily
    (D : Z → PeriodicQuaternionicData slots e b) (z₀ : Z) (U : Set Z) where
  open_parameter : IsOpen U
  base_mem : z₀ ∈ U
  forward : Z × E → E
  backward : Z × E → E
  sourceNeighborhood : Set (Z × E)
  targetNeighborhood : Set (Z × E)
  source_open : IsOpen sourceNeighborhood
  target_open : IsOpen targetNeighborhood
  source_parameter : sourceNeighborhood ⊆ U ×ˢ univ
  target_parameter : targetNeighborhood ⊆ U ×ˢ univ
  source_closed : U ×ˢ {x | (D z₀).defining x ≤ 0} ⊆ sourceNeighborhood
  target_closed : {p : Z × E | p.1 ∈ U ∧ (D p.1).defining p.2 ≤ 0} ⊆ targetNeighborhood
  forward_smooth : ContDiffOn ℝ ∞ forward sourceNeighborhood
  backward_smooth : ContDiffOn ℝ ∞ backward targetNeighborhood
  defining_smooth : ContDiffOn ℝ ∞ (fun p : Z × E => (D p.1).defining p.2) targetNeighborhood
  background_smooth : ContDiffOn ℝ ∞ (fun p : Z × E => (D p.1).background p.2) targetNeighborhood
  density_smooth : ContDiffOn ℝ ∞ (fun p : Z × E => (D p.1).density p.2) targetNeighborhood
  forward_mem : ∀ p ∈ sourceNeighborhood, (p.1,forward p) ∈ targetNeighborhood
  backward_mem : ∀ p ∈ targetNeighborhood, (p.1,backward p) ∈ sourceNeighborhood
  backward_forward : ∀ p ∈ sourceNeighborhood, backward (p.1,forward p) = p.2
  forward_backward : ∀ p ∈ targetNeighborhood, forward (p.1,backward p) = p.2
  forward_base : ∀ x, (z₀,x) ∈ sourceNeighborhood → forward (z₀,x) = x
  backward_base : ∀ x, (z₀,x) ∈ targetNeighborhood → backward (z₀,x) = x
  forward_strict : ∀ z ∈ U, ∀ x, (D z₀).defining x < 0 → (D z).defining (forward (z,x)) < 0
  backward_strict : ∀ z ∈ U, ∀ x, (D z).defining x < 0 → (D z₀).defining (backward (z,x)) < 0
  forward_closed : ∀ z ∈ U, ∀ x, (D z₀).defining x ≤ 0 → (D z).defining (forward (z,x)) ≤ 0
  backward_closed : ∀ z ∈ U, ∀ x, (D z).defining x ≤ 0 → (D z₀).defining (backward (z,x)) ≤ 0
  forward_periodic : ∀ z (l : Submodule.span ℤ (range b)) x,
    forward (z,x + e.symm ((l:P),0)) = forward (z,x) + e.symm ((l:P),0)
  backward_periodic : ∀ z (l : Submodule.span ℤ (range b)) x,
    backward (z,x + e.symm ((l:P),0)) = backward (z,x) + e.symm ((l:P),0)
  backward_first : ∀ z ∈ U, ∀ x, (e (backward (z,x))).1 = (e x).1
  defining_transverse : ∀ z p v, (D z).defining (e.symm (p,v)) = (D z).defining (e.symm (0,v))

variable {D : Z → PeriodicQuaternionicData slots e b} {z₀ : Z} {U : Set Z}

def LocalDirichletFamily.referenceClosure (_G : LocalDirichletFamily D z₀ U) : Set V :=
  {v | (D z₀).defining (e.symm (0,v)) ≤ 0}

theorem LocalDirichletFamily.mem_referenceClosure_iff
    (G : LocalDirichletFamily D z₀ U) (x : E) :
    (e x).2 ∈ G.referenceClosure ↔ (D z₀).defining x ≤ 0 := by
  change (D z₀).defining (e.symm (0,(e x).2)) ≤ 0 ↔ _
  rw [← G.defining_transverse z₀ (e x).1 (e x).2]
  simp only [Prod.eta, e.symm_apply_apply]

theorem LocalDirichletFamily.isCompact_referenceClosure
    (G : LocalDirichletFamily D z₀ U) : IsCompact G.referenceClosure := by
  have hc : IsClosed G.referenceClosure := isClosed_le
    ((D z₀).defining_smooth.continuous.comp (e.symm.continuous.comp
      (continuous_const.prodMk continuous_id))) continuous_const
  apply (D z₀).compact.of_isClosed_subset hc
  intro v hv
  have h := (D z₀).bounded (e.symm (0,v)) hv
  simpa only [e.apply_symm_apply] using h

theorem LocalDirichletFamily.backward_boundary
    (G : LocalDirichletFamily D z₀ U) {z : Z} (hz : z ∈ U) {y : E}
    (hy : (D z).defining y = 0) : (D z₀).defining (G.backward (z,y)) = 0 := by
  apply le_antisymm (G.backward_closed z hz y hy.le)
  by_contra h
  have hn : (D z₀).defining (G.backward (z,y)) < 0 := lt_of_not_ge h
  have hf := G.forward_strict z hz _ hn
  rw [G.forward_backward (z,y) (G.target_closed ⟨hz,hy.le⟩),hy] at hf
  exact (lt_irrefl 0) hf

theorem LocalDirichletFamily.forward_boundary
    (G : LocalDirichletFamily D z₀ U) {z : Z} (hz : z ∈ U) {x : E}
    (hx : (D z₀).defining x = 0) : (D z).defining (G.forward (z,x)) = 0 := by
  apply le_antisymm (G.forward_closed z hz x hx.le)
  by_contra h
  have hn : (D z).defining (G.forward (z,x)) < 0 := lt_of_not_ge h
  have hf := G.backward_strict z hz _ hn
  rw [G.backward_forward (z,x) (G.source_closed ⟨hz,hx.le⟩),hx] at hf
  exact (lt_irrefl 0) hf

theorem LocalDirichletFamily.forward_base_germ
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    (fun y => G.forward (z₀,y)) =ᶠ[𝓝 x] id := by
  have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
    (G.source_open.mem_nhds (G.source_closed ⟨G.base_mem,hx⟩))
  filter_upwards [hn] with y hy
  exact G.forward_base y hy

theorem LocalDirichletFamily.backward_base_germ
    (G : LocalDirichletFamily D z₀ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    (fun y => G.backward (z₀,y)) =ᶠ[𝓝 x] id := by
  have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
    (G.target_open.mem_nhds (G.target_closed ⟨G.base_mem,hx⟩))
  filter_upwards [hn] with y hy
  exact G.backward_base y hy

end OAI.Analysis.Fourier.WavePackets
