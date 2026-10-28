import OAI.Analysis.Fourier.WavePackets.PeriodicDirichletAssembly
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Existence

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped ContDiff ComplexOrder

/-- The actual C⁴ existence theorem, specialized to the data consumed by
the packet construction. Dimension and nonempty-fiber side conditions
are resolved here rather than left as additional analytic hypotheses. -/
theorem PeriodicQuaternionicData.exists_C4_potential
    {m : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V] [Fintype ι]
    {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    ∃ ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ, ContDiff ℝ 4 ψ ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b ψ ∧
      (∀ x, D.defining x = 0 → ψ x = D.background x) ∧
      (∀ x, D.defining x ≤ 0 →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      (∀ x, D.defining x ≤ 0 →
        OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = D.density x) := by
  cases m with
  | zero => have hm := D.dimension; omega
  | succ n =>
    let : FiniteDimensional ℝ P := b.finiteDimensional_of_finite
    let : FiniteDimensional ℝ V := finiteDimensional_transverse_of_split (e := e)
    by_cases hne : {x | D.defining x ≤ 0}.Nonempty
    · exact OAI.Analysis.PDE.Dirichlet.exists_periodic_moore_dirichlet_C4 e b D.compact
        D.defining_smooth D.background_smooth D.density_smooth
        D.defining_periodic D.background_periodic D.density_periodic
        D.bounded hne D.regular D.defining_positive D.background_nonnegative
        D.background_degenerate D.density_positive
    · refine ⟨D.background, D.background_smooth.of_le (by simp),
        D.background_periodic, ?_, ?_, ?_⟩
      · intro x hx; rfl
      · intro x hx; exact (hne ⟨x, hx⟩).elim
      · intro x hx; exact (hne ⟨x, hx⟩).elim

end OAI.Analysis.Fourier.WavePackets
