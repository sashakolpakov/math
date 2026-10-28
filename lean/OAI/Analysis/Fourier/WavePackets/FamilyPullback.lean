import OAI.Analysis.Fourier.WavePackets.Dirichlet.FamilyTheorem

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Topology ContDiff

variable {Z : Type} {P V ι : Type*} {m s : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {slots : Fin s → Quaternion ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData slots e b} {z₀ : Z} {U A : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m s

/-- Intrinsic joint boundary smoothness gives the manuscript's smooth
dependence after any of the given local closure pullbacks. -/
theorem DirichletFamilySmoothUpToBoundary.pullback
    {S : DirichletSolutionFamily D} (hS : DirichletFamilySmoothUpToBoundary D A S)
    (G : LocalDirichletFamily D z₀ U) (hUA : U ⊆ A)
    {z : Z} (hz : z ∈ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    ∃ Q : Set (Z × E), IsOpen Q ∧ (z,x) ∈ Q ∧
      ∃ u : Z × E → ℝ, ContDiffOn ℝ ∞ u Q ∧
        ∀ p ∈ Q, (D z₀).defining p.2 ≤ 0 →
          u p = (S p.1).u (G.forward p) := by
  obtain ⟨O,hO,hpO,v,hv,hve⟩ := hS z (hUA hz) (G.forward (z,x)) (G.forward_closed z hz x hx)
  let F : Z × E → Z × E := fun p => (p.1,G.forward p)
  have hF : ContDiffOn ℝ ∞ F G.sourceNeighborhood := contDiffOn_fst.prodMk G.forward_smooth
  let Q : Set (Z × E) := G.sourceNeighborhood ∩ F ⁻¹' O
  have hQ : IsOpen Q := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hc : ContinuousAt F p :=
      ((hF p hp.1).contDiffAt (G.source_open.mem_nhds hp.1)).continuousAt
    exact Filter.inter_mem (G.source_open.mem_nhds hp.1)
      (hc.preimage_mem_nhds (hO.mem_nhds hp.2))
  refine ⟨Q,hQ,⟨G.source_closed ⟨hz,hx⟩,hpO⟩,fun p => v (F p),
    hv.comp (hF.mono inter_subset_left) (fun _ hp => hp.2),?_⟩
  intro p hp hpr
  have hpU : p.1 ∈ U := (G.source_parameter hp.1).1
  exact hve (F p) hp.2 (hUA hpU) (G.forward_closed p.1 hpU p.2 hpr)

end OAI.Analysis.Fourier.WavePackets
