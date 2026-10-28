import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Coefficient

/-! A uniform normalized Hölder coefficient family, preserving the boundary. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem exists_boundary_normalized_holder_field {m : ℕ} {α ell Λ N : ℝ}
    (hα : 0 ≤ α) (hell : 0 < ell) (hΛ : 0 ≤ Λ) (_ : 0 ≤ N)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hAn : ‖A‖ ≤ N) (x₀ : EuclideanSpace ℝ (Fin m)) (k : Fin m)
    (hA : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef)
    (hlower : ∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖ ^ 2 ≤
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x))
    (hupper : ∀ x : EuclideanSpace ℝ (Fin m),
      inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x) ≤ Λ * ‖x‖ ^ 2) :
    ∃ (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
      (Q : Matrix (Fin m) (Fin m) ℝ) (c : ℝ),
      0 < c ∧ (∀ x, L x k = c * x k) ∧
      ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
      ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (normalizedHolderCoefficient hα A x₀ L.toContinuousLinearMap Q) 0 = 1 ∧
      ‖normalizedHolderCoefficient hα A x₀ L.toContinuousLinearMap Q‖ ≤
        ((m : ℝ)^2 * ((Real.sqrt ell)⁻¹)^2 * (1 + (Real.sqrt Λ)^α)) * N ∧
      (∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u → ∀ x,
        nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (normalizedHolderCoefficient hα A x₀ L.toContinuousLinearMap Q))
          (fun y => u (x₀ + L y)) x = nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u (x₀ + L x)) := by
  obtain ⟨L, P, Q, c, hc, hnormal, hP, hQ, hPQ, hQP, hQA, hLn, hLin, hQn⟩ :=
    exists_boundary_normalization_matrices (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) hA k hell hΛ hlower hupper
  refine ⟨L, Q, c, hc, hnormal, hLn, hLin, ?_, ?_, ?_⟩
  · simpa only [normalizedHolderCoefficient_value, map_zero, add_zero] using hQA
  · apply (norm_normalizedHolderCoefficient_le hα A x₀ L.toContinuousLinearMap Q).trans
    gcongr
  · intro u hu x
    have heq := nondivergence_conjugated_affine (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u hu P Q hPQ x₀ x
    have hLfun : (fun y => x₀ + Matrix.toEuclideanCLM (𝕜 := ℝ) P y) = (fun y => x₀ + L y) := by
      rw [hP]
      rfl
    change nondivergenceOperator (fun y => Q * OAI.Analysis.Normed.Function.Holder.HolderMap.value A (x₀ + L y) * Q.transpose)
      (fun y => u (x₀ + L y)) x = _
    simpa only [hLfun, hP, ContinuousLinearEquiv.coe_coe, normalizedHolderCoefficient_value] using heq

end OAI.Analysis.PDE.Schauder
