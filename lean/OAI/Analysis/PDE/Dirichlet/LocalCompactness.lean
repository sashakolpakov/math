import OAI.Analysis.PDE.Dirichlet.HolderCompactness
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Set Metric Filter Topology
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Arzelà--Ascoli on a locally compact second-countable domain, with one
subsequence converging locally uniformly everywhere, not one subsequence
for each chosen compact set. -/
theorem exists_locally_uniform_limit_of_equicontinuous
    {E Y : Type*} [TopologicalSpace E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup Y] [ProperSpace Y] [SecondCountableTopology Y]
    (u : ℕ → E → Y) (hu : ∀ k, Continuous (u k))
    {M : ℝ} (hbound : ∀ k x, ‖u k x‖ ≤ M) (heq : Equicontinuous u) :
    ∃ v : E → Y, Continuous v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun k ↦ u (φ k)) v atTop := by
  classical
  let f : ℕ → C(E, Y) := fun k ↦ ⟨u k, hu k⟩
  have hrange : ∀ g : Set.range f, ∃ k, g.val = f k := fun g ↦
    let ⟨k, hk⟩ := g.property
    ⟨k, hk.symm⟩
  choose j hj using hrange
  have heq' : Equicontinuous ((↑) : Set.range f → E → Y) := by
    convert heq.comp j using 1
    funext g x
    change g.val x = u (j g) x
    rw [hj g]
    rfl
  let : T2Space (UniformOnFun E Y {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hclosed : IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
      C(E, Y) → UniformOnFun E Y {K | IsCompact K}) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc : IsCompact (closure (range f)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := ((↑) : C(E, Y) → E → Y)) (fun K hK ↦ hK) hclosed
      (fun K _ ↦ heq'.equicontinuousOn K) (by
        intro K hK x hx
        refine ⟨closedBall (0 : Y) M, isCompact_closedBall _ _, ?_⟩
        intro g hg
        obtain ⟨k, rfl⟩ := hg
        rw [mem_closedBall, dist_zero_right]
        exact hbound k x)
  obtain ⟨v, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun k ↦ subset_closure (mem_range_self k))
  exact ⟨v, v.continuous, φ, hφ, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim⟩

end OAI.Analysis.PDE.Dirichlet
