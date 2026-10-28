import OAI.Analysis.PDE.Elliptic.Boundary.Third.NormalRecovery
import OAI.Analysis.Normed.Function.Holder.Boundary.LogCoefficient

/-! Quantitative recovery of the missing pure-normal third derivative.
The recovered field is a genuine Hölder extension of the derivative of
the smooth solution, not an independently postulated normal jet. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {X : Type*} [MetricSpace X] {α : ℝ}

def scalarHolderMul (hα : 0 ≤ α) (f g : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.lsmul ℝ ℝ) f g

@[simp] theorem value_scalarHolderMul (hα : 0 ≤ α) (f g : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (scalarHolderMul hα f g) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f x * OAI.Analysis.Normed.Function.Holder.HolderMap.value g x := rfl

theorem scalarHolderMul_norm_le (hα : 0 ≤ α) (f g : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α) :
    ‖scalarHolderMul hα f g‖ ≤ 2 * ‖f‖ * ‖g‖ := by
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_bilinear_le hα (ContinuousLinearMap.lsmul ℝ ℝ) f g).trans
  gcongr
  simp

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exists_pure_normal_third_holder
    {S : Set (EuclideanSpace ℝ I)} (hα : 0 ≤ α)
    {u : EuclideanSpace ℝ I → ℝ} (hu : ContDiff ℝ 3 u) (k : I)
    (a : EuclideanSpace ℝ I → Matrix I I ℝ)
    (A T : I × I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α) (R : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (hA : ∀ p (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (A p) x = a x p.1 p.2)
    (hT : ∀ p, p ≠ (k,k) → ∀ x : S,
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (T p) x = tangentThirdEntry u k p.1 p.2 x)
    {μ : ℝ} (hμ : 0 < μ) (hpos : ∀ x : S, μ ≤ a x k k)
    (heq : ∀ x : S, OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator a
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single k 1))) x
          (EuclideanSpace.single k 1) (EuclideanSpace.single k 1)) ∧
      ‖H‖ ≤ 2 * (μ⁻¹ + (μ*μ)⁻¹ * ‖A (k,k)‖) *
        (‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * ‖T p‖) := by
  obtain ⟨aI, haI, hnI⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_positive_reciprocal hα (A (k,k)) hμ
    (fun x => by rw [hA]; exact hpos x)
  let U := R - ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), scalarHolderMul hα (A p) (T p)
  have hU : ‖U‖ ≤ ‖R‖ + ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k), 2 * ‖A p‖ * ‖T p‖ := by
    apply (norm_sub_le _ _).trans
    apply add_le_add le_rfl
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => scalarHolderMul_norm_le hα (A p) (T p)))
  refine ⟨scalarHolderMul hα aI U, ?_, ?_⟩
  · intro x
    have hneq : a x k k ≠ 0 := (hμ.trans_le (hpos x)).ne'
    rw [value_scalarHolderMul, haI, hA, pure_normal_third_eq hu a k x _ hneq (heq x)]
    have hUv : OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = OAI.Analysis.Normed.Function.Holder.HolderMap.value R x -
        ∑ p ∈ (Finset.univ : Finset (I × I)).erase (k,k),
          a x p.1 p.2 * tangentThirdEntry u k p.1 p.2 x := by
      change OAI.Analysis.Normed.Function.Holder.HolderMap.valueCLM U x = _
      simp only [U, map_sub, map_sum, BoundedContinuousFunction.sub_apply,
        BoundedContinuousFunction.sum_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg₂ (fun a b : ℝ => a*b) (hA p x) (hT p (Finset.mem_erase.mp hp).1 x)
    rw [hUv]
    ring
  · exact (scalarHolderMul_norm_le hα aI U).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hnI (by norm_num)) hU (norm_nonneg _)
        (by positivity))

end OAI.Analysis.PDE.Elliptic
