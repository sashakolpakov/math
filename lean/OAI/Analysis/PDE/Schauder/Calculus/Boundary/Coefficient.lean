import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Normalization
import OAI.Analysis.PDE.Nonlinear.Dilation

/-! Hölder coefficients under a boundary-preserving linear normalization. -/

noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def normalizedHolderCoefficient {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (x₀ : EuclideanSpace ℝ (Fin m))
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin m) (Fin m) ℝ) :
    OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (matrixCongruenceCLM Q) (holderLinearAffinePullback hα A x₀ L)

@[simp] theorem normalizedHolderCoefficient_value {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (x₀ : EuclideanSpace ℝ (Fin m))
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (normalizedHolderCoefficient hα A x₀ L Q) x =
      Q * OAI.Analysis.Normed.Function.Holder.HolderMap.value A (x₀+L x) * Q.transpose := rfl

theorem norm_normalizedHolderCoefficient_le {m : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (x₀ : EuclideanSpace ℝ (Fin m))
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (Q : Matrix (Fin m) (Fin m) ℝ) :
    ‖normalizedHolderCoefficient hα A x₀ L Q‖ ≤
      ((m : ℝ)^2*‖Q‖^2*(1+‖L‖^α))*‖A‖ := by
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le (matrixCongruenceCLM Q) _).trans
  have hm := norm_matrixCongruenceCLM_le Q
  have ha := OAI.Analysis.PDE.Nonlinear.norm_holderLinearAffinePullback_le hα A x₀ L
  exact (mul_le_mul hm ha (norm_nonneg _) (by positivity)).trans_eq (by ring)

end OAI.Analysis.PDE.Schauder
