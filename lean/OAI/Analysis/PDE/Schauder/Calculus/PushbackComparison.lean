import OAI.Analysis.PDE.Schauder.Calculus.PhysicalPushback
import OAI.Analysis.PDE.Dirichlet.ContinuousComparison

open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Comparison identifies the implicit branch after pushing it to physical
coordinates. It requires no continuity of geometric composition in a Hölder norm. -/
theorem physicalPushback_identified
    (hn : 1 ≤ n) (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K) {r B₀ ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hB : ContDiff ℝ 2 B₀) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b B₀)
    (hψ : ContDiffOn ℝ 2 ψ {x | r x < 0}) (hψc : ContinuousOn ψ {x | r x ≤ 0})
    (hψp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b ψ)
    (hψpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hψbd : ∀ x, r x = 0 → ψ x = B₀ x)
    {Φ Ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hΨ : ContDiff ℝ 2 Ψ) (hleft : Function.LeftInverse Ψ Φ)
    (hΦlevel : ∀ x, r (Φ x) = r x) (hΨlevel : ∀ x, r (Ψ x) = r x)
    (hΨp : ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Ψ (x+e.symm ((l:P),0)) = Ψ x+e.symm ((l:P),0))
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (hvpos : ∀ x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ Ψ v) x)).PosDef)
    (hvdet : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (physicalPushback B₀ Ψ v) x) =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) :
    ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val x = ψ (Φ x)-B₀ (Φ x) := by
  have heq := OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice hn e b hK
    (contDiffOn_physicalPushback hr.continuous hB hΨ hΨlevel v) hψ hr
    (continuousOn_physicalPushback hB.continuous hΨ.continuous hΨlevel v) hψc hbounded
    hrp (latticePeriodic_physicalPushback hBp hΨp v) hψp hrpos hvpos hψpos hvdet
    (fun x hx => (physicalPushback_boundary hΨlevel v hx).trans (hψbd x hx).symm)
  intro x
  rw [← physicalPushback_pullback hleft v x,heq (Φ x)]
  simpa only [Set.mem_ofPred_eq,hΦlevel] using x.property

end OAI.Analysis.PDE.Schauder
