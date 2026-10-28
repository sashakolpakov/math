import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Regular
import OAI.Analysis.Normed.Function.Holder.SmoothPeriodicExtensionJets
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

/-! Actual smooth periodic representatives of closed-domain Banach jets. -/

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {m N : ℕ} {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_latticeDirichlet_classical_representative
    (hm : 0 < m) (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] E)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    (r : E → ℝ) (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (hU : U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e b)
    (hN : 2 ≤ N)
    (hf : ContDiffOn ℝ N (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x ≤ 0}) :
    ∃ g : E → ℝ, ContDiff ℝ N g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      (∀ x, r x = 0 → g x = 0) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = g x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ g x) ∧
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
        fderiv ℝ (fderiv ℝ g) x) := by
  have hper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) := hU.2
  obtain ⟨g, hg, hgp, hgeq⟩ := exists_latticePeriodic_extension_regular_sublevel_equiv hm L
    e b hC r hr hrp hbounded hreg (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) hper hf
  have heq : ∀ x : {x | r x ≤ 0}, g x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x := by
    intro x
    simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] using hgeq x x.property
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  obtain ⟨hfirst, hsecond⟩ := OAI.Analysis.Normed.Function.Holder.C2Holder.classical_extension_derivatives
    (isOpen_lt hr.continuous continuous_const) hclosure U g
    (hg.of_le (by exact_mod_cast hN)) heq
  refine ⟨g, hg, hgp, ?_, (fun x => (heq x).symm),
    (fun x => (hfirst x).symm), (fun x => (hsecond x).symm)⟩
  intro x hx
  rw [heq ⟨x, hx.le⟩]
  exact hU.1 ⟨x, hx.le⟩ (by simp only [Set.mem_ofPred_eq, hx, lt_self_iff_false, not_false_eq_true])

end OAI.Analysis.Calculus.SmoothExtension
