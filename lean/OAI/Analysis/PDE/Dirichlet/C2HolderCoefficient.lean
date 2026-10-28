import OAI.Analysis.PDE.Dirichlet.Moore.RealOperator
import OAI.Analysis.Normed.Function.Holder.Banach.Composition

open Set
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

/-- The real coefficient field of the true nonlinear derivative belongs to
C^α, with a norm bound uniform on every C²,α ball of potentials. -/
theorem exists_detRealCoefficient_bound {n : ℕ}
    {Ω K : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖f‖ ≤ R →
      ∃ a : OAI.Analysis.Normed.Function.Holder.HolderMap K (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α,
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x =
          detRealOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f) x)) ∧
        ‖a‖ ≤ C := by
  let J := quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots
  obtain ⟨C, hC, hcompose⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := K) (contDiff_detRealOperator n 1) hα (mul_nonneg (norm_nonneg J) hR)
  refine ⟨C * (1 + ‖J‖ * R), mul_nonneg hC (by positivity), ?_⟩
  intro f hf
  have hJ : ‖J f‖ ≤ ‖J‖ * R := (J.le_opNorm f).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg J))
  obtain ⟨a, ha, hnorm⟩ := hcompose (J f) hJ
  refine ⟨a, ha, hnorm.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (by linarith) hC

theorem exists_detRealCoefficient {n : ℕ}
    {Ω K : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :
    ∃ a : OAI.Analysis.Normed.Function.Holder.HolderMap K (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α,
      ∀ x : CoordinateSpace n 4, ∀ hx : x ∈ Ω,
        OAI.Analysis.Normed.Function.Holder.HolderMap.value a ⟨x, hΩK hx⟩ =
          detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
            (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) x) := by
  obtain ⟨C, hC, hall⟩ := exists_detRealCoefficient_bound (hΩK := hΩK) hα (norm_nonneg f)
  obtain ⟨a, ha, hnorm⟩ := hall f le_rfl
  refine ⟨a, ?_⟩
  intro x hx
  rw [ha, quaternionHessianField_eq hΩ hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots f hx]

end OAI.Analysis.PDE.Dirichlet
