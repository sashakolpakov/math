import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.C2Representative
import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : CoordinateSpace n 4 → ℝ} {α : ℝ}
  {e : CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => CoordinateSpace n 4
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

local instance roughC2RepDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance roughC2RepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance roughC2RepSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance roughC2RepSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The full rough potential has a genuine global C² representative with
the prescribed boundary data and the exact closed-domain Banach jets. -/
theorem exists_full_potential_C2_representative [Nontrivial E]
    (hn : 1 ≤ n) {K : Set V} (hK : IsCompact K)
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 2 B₀) (hB₀p : LatticePeriodic e b B₀)
    (B : H)
    (hB₀v : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value B x = B₀ x)
    (hB₁ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative B x = fderiv ℝ B₀ x)
    (hB₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (u : X) :
    ∃ ψ : E → ℝ, ContDiff ℝ 2 ψ ∧ LatticePeriodic e b ψ ∧
      (∀ x, r x = 0 → ψ x = B₀ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (B+u.val) x = ψ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (B+u.val) x = fderiv ℝ ψ x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (B+u.val) x =
        fderiv ℝ (fderiv ℝ ψ) x) := by
  obtain ⟨v,hv,hvp,hvbd,hv₀,hv₁,hv₂⟩ := exists_latticeDirichlet_C2_representative
    (m := n*4) (by omega) (flattenFourSlots n).symm.toContinuousLinearEquiv e b hK
    r hr hrp hbounded hreg u.val u.property
  refine ⟨B₀+v,hB₀.add hv,hB₀p.add hvp,?_,?_,?_,?_⟩
  · intro x hx
    simp only [Pi.add_apply,hvbd x hx,add_zero]
  · intro x
    change OAI.Analysis.Normed.Function.Holder.C2Holder.value B x+OAI.Analysis.Normed.Function.Holder.C2Holder.value u.val x = B₀ x+v x
    rw [hB₀v,hv₀]
  · intro x
    change OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative B x+OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative u.val x = _
    rw [hB₁,hv₁,fderiv_add (hB₀.differentiable (by norm_num) x) (hv.differentiable (by norm_num) x)]
  · intro x
    change OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x+OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u.val x = _
    rw [hB₂,hv₂]
    exact (second_fderiv_add hB₀ hv x).symm

end OAI.Analysis.PDE.Dirichlet
