import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Lift
import OAI.Analysis.Normed.Function.Holder.C2HolderOperator

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance latticeJetsDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance latticeJetsDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance latticeJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance latticeJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

structure LatticeJetLifts {r : E → ℝ} (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    (α : ℝ) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) where
  first : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b →L[ℝ]
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α
  second : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b →L[ℝ]
    OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α
  first_value : ∀ U, OAI.Analysis.Normed.Function.Holder.HolderMap.value (first U) = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U.val
  second_value : ∀ U, OAI.Analysis.Normed.Function.Holder.HolderMap.value (second U) = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U.val
  first_periodic : ∀ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (first U)))
  second_periodic : ∀ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (second U)))

theorem nonempty_latticeJetLifts
    (hn : 0 < n) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r : E → ℝ} (hr : ContDiff ℝ ∞ r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Nonempty (LatticeJetLifts hΩK α e b) := by
  obtain ⟨D₁,hD₁⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.exists_lattice_gradient_holder_clm hn e b hK hr hrp hbounded hreg hΩK hα hα1
  let D₂ := OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM.comp (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
  have hD₂ U : OAI.Analysis.Normed.Function.Holder.HolderMap.value (D₂ U) = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U.val := rfl
  have hopen : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hKΩ : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  have hpΩ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => x ∈ {x | r x < 0}) := by
    intro x l
    change (r (e.symm ((e x).1+(l:P),(e x).2)) < 0) = (r x < 0)
    rw [hrp x l]
  have hpK : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => x ∈ {x | r x ≤ 0}) := by
    intro x l
    change (r (e.symm ((e x).1+(l:P),(e x).2)) ≤ 0) = (r x ≤ 0)
    rw [hrp x l]
  refine ⟨⟨D₁,D₂,hD₁,hD₂,?_,?_⟩⟩
  · intro U
    rw [hD₁]
    exact OAI.Analysis.Normed.Function.Holder.C2Holder.latticePeriodic_firstDerivative hopen hKΩ hpΩ hpK U.val U.property.2
  · intro U
    rw [hD₂]
    exact OAI.Analysis.Normed.Function.Holder.C2Holder.latticePeriodic_secondDerivative hopen hKΩ hpΩ hpK U.val U.property.2

end OAI.Analysis.PDE.Schauder
