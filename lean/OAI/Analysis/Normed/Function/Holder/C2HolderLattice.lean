import OAI.Analysis.Normed.Function.Holder.C2HolderDirichlet
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

open Set Module
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

omit [NormedSpace ℝ E] in
theorem continuous_zeroExtension_evaluation (x : E) :
    Continuous (fun f : K →ᵇ ℝ ↦ boundedZeroExtension f x) := by
  by_cases hx : x ∈ K
  · simp only [boundedZeroExtension_apply _ hx]
    exact (BoundedContinuousFunction.evalCLM ℝ (⟨x, hx⟩ : K)).continuous
  · have heq : (fun f : K →ᵇ ℝ ↦ boundedZeroExtension f x) = fun _ ↦ 0 := by
      funext f
      simp [boundedZeroExtension, OAI.Analysis.PDE.Dirichlet.zeroExtend, hx]
    rw [heq]
    exact continuous_const

/-- Periodicity for the actual zero-extended functions, with an arbitrary
lattice basis and coordinate splitting. -/
def latticeBCF (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) : Submodule ℝ (K →ᵇ ℝ) where
  carrier := {f | OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension f)}
  zero_mem' := by
    change OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (0 : K →ᵇ ℝ))
    rw [boundedZeroExtension_zero]
    intro x l
    rfl
  add_mem' := by
    intro f g hf hg
    change OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (f + g))
    rw [boundedZeroExtension_add]
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (boundedZeroExtension (c • f))
    rw [boundedZeroExtension_smul]
    exact hf.smul c

omit [Fintype ι] in
theorem isClosed_latticeBCF (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    IsClosed (latticeBCF (K := K) e b : Set (K →ᵇ ℝ)) := by
  change IsClosed {f : K →ᵇ ℝ | ∀ (x : E) (l : Submodule.span ℤ (Set.range b)),
    boundedZeroExtension f (e.symm ((e x).1 + (l : P), (e x).2)) = boundedZeroExtension f x}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro l
  exact isClosed_eq (continuous_zeroExtension_evaluation _) (continuous_zeroExtension_evaluation x)

def latticeHolder (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) : Submodule ℝ (HolderMap K ℝ α) :=
  (latticeBCF e b).comap OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.toLinearMap

omit [Fintype ι] in
theorem isClosed_latticeHolder (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    IsClosed (latticeHolder (K := K) (α := α) e b : Set (HolderMap K ℝ α)) :=
  (isClosed_latticeBCF e b).preimage OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM.continuous

abbrev LatticeHolderSpace (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) : Type _ :=
  ↥(latticeHolder (K := K) (α := α) e b)

instance (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    CompleteSpace (LatticeHolderSpace (K := K) (α := α) e b) :=
  (isClosed_latticeHolder (K := K) (α := α) e b).isComplete.completeSpace_coe

namespace C2Holder

def latticeDirichlet (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    Submodule ℝ (C2Holder (F := ℝ) hΩK α) :=
  C2Holder.zeroTrace ⊓ (latticeBCF e b).comap C2Holder.valueCLM.toLinearMap

omit [Fintype ι] in
theorem isClosed_latticeDirichlet (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    IsClosed (C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b : Set (C2Holder (F := ℝ) hΩK α)) :=
  C2Holder.isClosed_zeroTrace.inter ((isClosed_latticeBCF e b).preimage C2Holder.valueCLM.continuous)

/-- The complete domain space used for the periodic Dirichlet inverse. -/
abbrev LatticeDirichletSpace (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) : Type _ :=
  ↥(C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b)

instance [Fact (IsOpen Ω)] (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    CompleteSpace (C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :=
  (C2Holder.isClosed_latticeDirichlet (hΩK := hΩK) (α := α) e b).isComplete.completeSpace_coe

end C2Holder
end OAI.Analysis.Normed.Function.Holder
