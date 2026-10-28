import OAI.Analysis.PDE.Dirichlet.Periodic.DerivativeInjective

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Strictly positive quaternionic Hessians supply the defining-function
barrier needed for injectivity of the actual periodic derivative. -/
theorem fderiv_periodicMooreDirichletOperator_injective
    (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hΩper : LatticePeriodic e lat (fun x ↦ r x < 0))
    (hKper : LatticePeriodic e lat (fun x ↦ r x ≤ 0))
    (hα : 0 ≤ α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e lat)
    (hpos : ∀ x (hx : r x < 0), (OAI.LinearAlgebra.Moore.complexify
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (v + u.val)) ⟨x, hΩK hx⟩)).PosDef)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef) :
    Function.Injective (fderiv ℝ (periodicMooreDirichletOperator
      (isOpen_lt hr.continuous continuous_const) hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots v hv) u) := by
  apply fderiv_periodicMooreDirichletOperator_injective_of_barrier
    e lat hC hr hrper hbounded hclosure hΩper hKper hα v hv u hpos
  intro x hx
  apply OAI.LinearAlgebra.Moore.mooreDifferential_pos_of_posDef _ _ (hpos x hx) (hrpos x hx).posSemidef
  intro he
  have hd := (hrpos x hx).diag_pos (i := (⟨0, hn⟩, 0))
  rw [he, OAI.LinearAlgebra.Moore.complexify_zero] at hd
  exact (lt_irrefl 0) (by simp at hd)

end OAI.Analysis.PDE.Dirichlet
