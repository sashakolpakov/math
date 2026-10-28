import OAI.Analysis.PDE.Nonlinear.Family
import OAI.Analysis.PDE.Nonlinear.SegmentPositive

/-! Actual real-matrix coefficient family, with its equation and ellipticity. -/

noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Weak

local instance matrixFamilyMapNormedGroup (n : ℕ) :
    NormedAddCommGroup ((OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ]
      Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) →L[ℝ]
    ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))

theorem exists_moore_matrix_family {n : ℕ} {α : ℝ} (hα : 0 < α)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 2 u)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)
    (v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) :
    ∃ B : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α,
      (∀ h x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x = OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (segmentOperator
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v)))) ∧
      (∃ M ≥ 0, ∀ h, ‖B h‖ ≤ M) ∧
      (∀ x, Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x) (𝓝 0)
        (𝓝 (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x))))) ∧
      (∀ h x, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef →
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v))).PosDef →
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x).PosDef) ∧
      (∀ h x, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x →
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v)) = f (x + h • v) →
        OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h)) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
          OAI.Analysis.PDE.Weak.differenceQuotient v h f x) := by
  obtain ⟨A, hA, ⟨M, hM, hb⟩, hlim, heq⟩ := exists_moore_difference_family hα u f hu H hH v
  let T := (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (n := n) (s := 4)).toContinuousLinearMap
  let B := fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM T (A h)
  have hval (h) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x = OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (segmentOperator
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (x + h • v))) := by
    change T (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x) = _
    rw [hA h x]
    rfl
  refine ⟨B, hval, ⟨‖T‖ * M, mul_nonneg (norm_nonneg T) hM, ?_⟩, ?_, ?_, ?_⟩
  · intro h
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le T (A h)).trans (mul_le_mul_of_nonneg_left (hb h) (norm_nonneg T))
  · intro x
    exact T.continuous.continuousAt.tendsto.comp (hlim x)
  · intro h x hx hx'
    rw [hval h x]
    exact segmentOperator_coordinate_posDef _ _ hx hx'
  · intro h x hx hx'
    have hs : (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x).toLinearMap.IsSymmetric := by
      rw [hA h x]
      exact segmentOperator_isSymmetric _ _
    have ht := ellipticTrace_eq_indexedNondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h))
      (OAI.Analysis.PDE.Weak.differenceQuotient v h u) (OAI.Analysis.PDE.Schauder.contDiff_differenceQuotient u hu v h) x hs
    exact ht.symm.trans (heq h x hx hx')

end OAI.Analysis.PDE.Nonlinear
