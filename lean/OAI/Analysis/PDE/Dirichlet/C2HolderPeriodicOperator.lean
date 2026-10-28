import OAI.Analysis.PDE.Dirichlet.C2HolderNonlinear
import OAI.Analysis.Normed.Function.Holder.C2HolderPeriodicity

open Set Module
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
theorem mooreDirichletOperator_latticePeriodic
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f))) :
    LatticePeriodic e b
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (mooreDirichletOperator hα slots f))) := by
  apply OAI.Analysis.Normed.Function.Holder.latticePeriodic_boundary_field hΩK hKΩ hΩper hKper
    ((hf.quaternionHessian slots).comp (OAI.LinearAlgebra.Moore.mooreDet m))
  intro x hx
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK hx)]
  exact mooreDirichletOperator_eq hΩ hα slots f hx

/-- The genuine nonlinear Dirichlet map with arbitrary lattice-periodic
domain and codomain, translated by a fixed periodic background. -/
def periodicMooreDirichletOperator
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b) :
    OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b := by
  refine ⟨mooreDirichletOperator hα slots (v + u.val), ?_⟩
  apply mooreDirichletOperator_latticePeriodic hΩ hKΩ hΩper hKper hα slots
  change LatticePeriodic e b
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v + OAI.Analysis.Normed.Function.Holder.C2Holder.value u.val))
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_add]
  exact hv.add u.property.2

end OAI.Analysis.PDE.Dirichlet
