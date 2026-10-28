import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Bounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def pullbackEllipticOperator (T A : E →L[ℝ] E) : E →L[ℝ] E :=
  T.comp (A.comp T.adjoint)

theorem pullbackEllipticOperator_form (T A : E →L[ℝ] E) (v : E) :
    inner ℝ v (pullbackEllipticOperator T A v) = inner ℝ (T.adjoint v) (A (T.adjoint v)) := by
  exact (T.adjoint_inner_left (A (T.adjoint v)) v).symm

omit [CompleteSpace E] in
theorem near_identity_norm_bounds (T : E →L[ℝ] E)
    (hT : ‖T - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) (v : E) :
    ‖v‖ / 2 ≤ ‖T v‖ ∧ ‖T v‖ ≤ (3 / 2) * ‖v‖ := by
  have hd : ‖T v - v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    have hh := (T - ContinuousLinearMap.id ℝ E).le_opNorm v
    simp only [sub_apply, ContinuousLinearMap.id_apply] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hh := abs_le.mp ((abs_norm_sub_norm_le (T v) v).trans hd)
  constructor <;> linarith

theorem adjoint_near_identity (T : E →L[ℝ] E)
    (hT : ‖T - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2) :
    ‖T.adjoint - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 := by
  have hh : ‖(T - ContinuousLinearMap.id ℝ E).adjoint‖ ≤ 1 / 2 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hT
  simpa only [map_sub, ContinuousLinearMap.adjoint_id] using hh

/-- A C¹ change of coordinates with Jacobian within 1/2 of the identity
preserves ellipticity with explicit constants. -/
theorem pullbackEllipticOperator_bounds (T A : E →L[ℝ] E)
    {lam L : ℝ} (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (hT : ‖T - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2)
    (hlo : ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (hhi : ∀ v : E, inner ℝ v (A v) ≤ L * ‖v‖ ^ 2) (v : E) :
    (lam / 4) * ‖v‖ ^ 2 ≤ inner ℝ v (pullbackEllipticOperator T A v) ∧
      inner ℝ v (pullbackEllipticOperator T A v) ≤ (9 * L / 4) * ‖v‖ ^ 2 := by
  rw [pullbackEllipticOperator_form]
  have hn := near_identity_norm_bounds T.adjoint (adjoint_near_identity T hT) v
  have hslo : ‖v‖ ^ 2 / 4 ≤ ‖T.adjoint v‖ ^ 2 := by nlinarith [norm_nonneg v, norm_nonneg (T.adjoint v)]
  have hshi : ‖T.adjoint v‖ ^ 2 ≤ (9 / 4) * ‖v‖ ^ 2 := by nlinarith [norm_nonneg v, norm_nonneg (T.adjoint v)]
  have hl := (mul_le_mul_of_nonneg_left hslo hlam).trans (hlo (T.adjoint v))
  have hh := (hhi (T.adjoint v)).trans (mul_le_mul_of_nonneg_left hshi hL)
  constructor <;> nlinarith

end OAI.Analysis.PDE.Elliptic
