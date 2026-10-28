import OAI.Analysis.PDE.Dirichlet.Linear.Continuous
import OAI.Analysis.Normed.Function.Holder.C2HolderExt
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The linearized Dirichlet operator has trivial kernel on the actual
closed-domain Hölder space, without assuming a smooth global extension. -/
theorem moore_linearized_banach_eq_zero
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    (hA : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (A x)).PosDef)
    (hrL : ∀ x, r x < 0 → 0 < mooreLinearization A r x)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hu : u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (hLu : ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u) x) = 0) :
    u = 0 := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hL (x) (hx : r x < 0) :
      mooreLinearization A (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u)) x = 0 := by
    unfold mooreLinearization
    rw [← quaternionHessianField_eq hΩ hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u hx]
    exact hLu ⟨x, hΩK hx⟩
  have hb (x) (hx : r x = 0) : OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) x = 0 := by
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) hx.le]
    exact hu.1 ⟨x, hx.le⟩ (by simp only [Set.mem_ofPred_eq, hx, lt_self_iff_false, not_false_eq_true])
  have hz := moore_linearized_zero_continuous_lattice e lat hC hr
    (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ u) (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _) hrper hu.2
    hbounded hA hL hrL hb
  apply OAI.Analysis.Normed.Function.Holder.C2Holder.value_injective hclosure
  apply BoundedContinuousFunction.ext
  intro x
  change OAI.Analysis.Normed.Function.Holder.C2Holder.value u x = 0
  have h := hz x x.property
  simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] using h

end OAI.Analysis.PDE.Dirichlet
