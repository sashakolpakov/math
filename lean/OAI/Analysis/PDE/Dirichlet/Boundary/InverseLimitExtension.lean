import OAI.Analysis.PDE.Dirichlet.SmoothPeriodicExtensionPath
import OAI.Analysis.PDE.Schauder.Dirichlet.UniformThirdRegularity

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.Calculus.SmoothExtension OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4

theorem BanachPathLimit.exists_C3_positive_representative
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
    {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩD β s t)
    (hthree : ContDiffOn ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0}) :
    ∃ ψ : E → ℝ, ContDiff ℝ 3 ψ ∧ LatticePeriodic e lat ψ ∧
      (∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD β OAI.Analysis.Calculus.Quaternion.fourSlots L.value) x =
          quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) := by
  obtain ⟨ψ,hψ,hψp,hψeq⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_latticePeriodic_extension_regular_sublevel_equiv
    (m := n*4) (by omega) (flattenFourSlots n).symm.toContinuousLinearEquiv e lat hK
    r hr hrp hbounded hreg (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) L.periodic hthree
  have heq (x : {x | r x ≤ 0}) : ψ x = OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value x := by
    simpa only [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ x.property] using hψeq x x.property
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  have hjets := OAI.Analysis.Normed.Function.Holder.C2Holder.classical_extension_derivatives
    (isOpen_lt hr.continuous continuous_const) hclosure L.value ψ
    (hψ.of_le (by norm_num)) heq
  have hfield (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD β OAI.Analysis.Calculus.Quaternion.fourSlots L.value) x =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots L.value ψ x (hjets.2 x).symm
  refine ⟨ψ,hψ,hψp,hfield,?_⟩
  intro x hx
  rw [← hfield ⟨x,hx⟩]
  exact (L.admissible ⟨x,hx⟩).2

end OAI.Analysis.PDE.Dirichlet
