import OAI.Analysis.PDE.Dirichlet.ContinuousComparison
import OAI.Analysis.Normed.Function.Holder.C2HolderExt
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.PDE.Dirichlet.Closed.Admissible

open Set Module
open scoped BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniqueness also holds for the actual closed-domain Hölder limits,
even when the two representatives use different Hölder exponents. -/
theorem quaternionic_dirichlet_banach_values_unique (hn : 1 ≤ n)
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 2 r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hrper : LatticePeriodic e lat r)
    (hrpos : ∀ x, r x < 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α β : ℝ}
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK β)
    (hu : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u)))
    (hv : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (hupos : ∀ x : {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u) x)).PosDef)
    (hvpos : ∀ x : {x | r x ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots v) x)).PosDef)
    (hdet : ∀ x : {x | r x ≤ 0},
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u) x) =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots v) x))
    (hbd : ∀ x : {x | r x ≤ 0}, r x = 0 → OAI.Analysis.Normed.Function.Holder.C2Holder.value u x = OAI.Analysis.Normed.Function.Holder.C2Holder.value v x) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value u = OAI.Analysis.Normed.Function.Holder.C2Holder.value v := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hup (x) (hx : r x < 0) :
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u)) x)).PosDef := by
    rw [← quaternionHessianField_eq hΩ hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u hx]
    exact hupos ⟨x, hΩK hx⟩
  have hvp (x) (hx : r x < 0) :
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)) x)).PosDef := by
    rw [← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots v hx]
    exact hvpos ⟨x, hΩK hx⟩
  have hd (x) (hx : r x < 0) :
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u)) x) =
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)) x) := by
    rw [← quaternionHessianField_eq hΩ hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots u hx,
      ← quaternionHessianField_eq hΩ hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots v hx]
    exact hdet ⟨x, hΩK hx⟩
  have hb (x) (hx : r x = 0) :
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) x = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v) x := by
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (x := x) (OAI.Analysis.Normed.Function.Holder.C2Holder.value u) hx.le,
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (x := x) (OAI.Analysis.Normed.Function.Holder.C2Holder.value v) hx.le]
    exact hbd ⟨x, hx.le⟩ hx
  have heq := quaternionic_dirichlet_uniqueness_continuous_lattice hn e lat hC
    (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ u) (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ v) hr
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _) (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _) hbounded
    hrper hu hv hrpos hup hvp hd hb
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] using heq x x.property

end OAI.Analysis.PDE.Dirichlet
