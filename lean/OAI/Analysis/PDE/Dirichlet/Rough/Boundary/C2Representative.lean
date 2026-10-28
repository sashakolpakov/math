import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Holder
import OAI.Analysis.PDE.Dirichlet.Closed.C2Regularity

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Nontrivial E] in
/-- Every actual periodic zero-Dirichlet C²,α jet has a global periodic C²
representative, with exactly its value and its first two derivatives on the
closed domain. No third derivative of the jet is assumed. -/
theorem exists_latticeDirichlet_C2_representative
    (hm : 0 < m) (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    (r : E → ℝ) (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hU : U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e b) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ LatticePeriodic e b g ∧
      (∀ x, r x = 0 → g x = 0) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = g x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ g x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
        fderiv ℝ (fderiv ℝ g) x) := by
  exact OAI.Analysis.Calculus.SmoothExtension.exists_latticeDirichlet_classical_representative hm L e b hC
    r hr hrp hbounded hreg U hU (by norm_num)
    (c2Holder_contDiffOn_two_closed (hr.of_le (by simp)) hreg U)

end OAI.Analysis.PDE.Dirichlet
